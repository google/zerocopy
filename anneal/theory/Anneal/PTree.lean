-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic

/-!
# Canonical Positive Binary Radix Trie (`Anneal.PTree`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`,
computable `@Nat.rec` top-down tabulation `ptreeTabulate` and `natToPosAt` with
`hasIR = true`, allowed theory tactics only) Appel-Leroy canonical positive
radix trie `PTree α`:

- Every finite map has a unique canonical representation
  (`RawTree.isCanon = true`), giving axiom-free extensional equality
  `ptree_eq_of_get` (zero Lean axioms: no `funext`, no `Classical.choice`, no
  `Quot.sound`) so disjoint updates commute definitionally (`rfl`) on concrete
  keys.
- Top-down strided `ptreeTabulate` builds canonical radix tries lazily in
  `O(log N)` forced WHNF nodes per lookup, avoiding the `O(N)` stack and WHNF
  blowup of sequential `List.foldl PTree.set` on large CFG tables.
- Polymorphic `PTree.diffWith eqB` implements deterministic, non-backtracking
  structural map subtraction over `req` (one recursive call per `req` node),
  usable for separation-logic framing (`ptree_diffWith_sound`).
-/

namespace Anneal.PTree

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a with
  | false => cases b <;> nomatch h
  | true => rfl

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => cases b <;> nomatch h
  | true => exact h

/-! ## 1. Positive Binary Keys (`Pos`) -/

/-- Positive binary number key (`xH` = `1`, `xO p` = `2 * p`,
`xI p` = `2 * p + 1`) indexing bits from least to most significant. -/
inductive Pos where
  | xH
  | xO (p : Pos)
  | xI (p : Pos)

/-- Structural Boolean equality on positive binary keys `Pos`. Marked
`noncomputable` to avoid compiler `._unsafe_rec` auxiliaries while remaining
definitionally reducible in kernel proofs. -/
noncomputable def Pos.beq : Pos → Pos → Bool
  | .xH, .xH => true
  | .xO a, .xO b => Pos.beq a b
  | .xI a, .xI b => Pos.beq a b
  | _, _ => false

/-- Reflexivity of `Pos.beq`. -/
theorem posBeq_refl : ∀ p : Pos, Pos.beq p p = true
  | .xH => rfl
  | .xO p => posBeq_refl p
  | .xI p => posBeq_refl p

/-- Propositional equality from `Pos.beq a b = true`. -/
theorem pos_eq_of_beq : ∀ {a b : Pos}, Pos.beq a b = true → a = b
  | .xH, .xH, _ => rfl
  | .xO _, .xO _, h => congrArg Pos.xO (pos_eq_of_beq h)
  | .xI _, .xI _, h => congrArg Pos.xI (pos_eq_of_beq h)
  | .xH, .xO _, h => by nomatch h
  | .xH, .xI _, h => by nomatch h
  | .xO _, .xH, h => by nomatch h
  | .xO _, .xI _, h => by nomatch h
  | .xI _, .xH, h => by nomatch h
  | .xI _, .xO _, h => by nomatch h

/-- Binary successor on `Pos`. -/
noncomputable def Pos.succ : Pos → Pos
  | .xH => .xO .xH
  | .xO p => .xI p
  | .xI p => .xO (Pos.succ p)

/-- Inject `Nat` (`n ≥ 0`) bijectively into `Pos` (`n + 1`). -/
noncomputable def natToPos : Nat → Pos
  | 0 => .xH
  | n + 1 => Pos.succ (natToPos n)

/-- Interpret a positive binary key `Pos` as its positive `Nat` value. -/
noncomputable def posToNat : Pos → Nat
  | .xH => 1
  | .xO p => 2 * posToNat p
  | .xI p => 2 * posToNat p + 1

/-- `posToNat` commutes with `Pos.succ` as `+ 1`. -/
theorem posToNat_succ : ∀ p : Pos, posToNat (Pos.succ p) = posToNat p + 1
  | .xH => rfl
  | .xO _ => rfl
  | .xI p => by
    dsimp only [Pos.succ, posToNat]
    rw [posToNat_succ p, Nat.mul_add 2 (posToNat p) 1]

/-- `posToNat` is a left inverse to `natToPos` shifted by `+ 1`. -/
theorem posToNat_natToPos : ∀ n : Nat, posToNat (natToPos n) = n + 1
  | 0 => rfl
  | n + 1 => by
    dsimp only [natToPos]
    rw [posToNat_succ, posToNat_natToPos n]

/-- `natToPos` is injective, ensuring distinct `Nat` indices yield distinct
`Pos` keys. -/
theorem natToPos_inj {m n : Nat} (h : natToPos m = natToPos n) : m = n := by
  have h1 : posToNat (natToPos m) = posToNat (natToPos n) :=
    congrArg posToNat h
  rw [posToNat_natToPos m, posToNat_natToPos n] at h1
  exact Nat.succ.inj h1

/-! ## 2. Canonical `RawTree` and `PTree` -/

/-- Unconstrained binary radix trie node representation indexed by `Pos`. -/
inductive RawTree (α : Type) where
  | leaf
  | node (l : RawTree α) (v : Option α) (r : RawTree α)

/-- Return `true` iff `t` is `.leaf`. -/
def RawTree.isLeaf {α : Type} : RawTree α → Bool
  | .leaf => true
  | .node _ _ _ => false

/-- Return `true` iff every node in `t` has canonical shape (no `.node .leaf
none .leaf` empty branches) and both children are canonical. -/
noncomputable def RawTree.isCanon {α : Type} : RawTree α → Bool
  | .leaf => true
  | .node l v r =>
    match v with
    | none => (!(l.isLeaf && r.isLeaf)) && l.isCanon && r.isCanon
    | some _ => l.isCanon && r.isCanon

/-- Left child of a canonical `.node` is canonical. -/
theorem rawTree_isCanon_left {α : Type} {l r : RawTree α} {v : Option α}
    (h : (RawTree.node l v r).isCanon = true) : l.isCanon = true := by
  cases v with
  | none =>
    dsimp only [RawTree.isCanon] at h
    exact bool_and_right (bool_and_left h)
  | some _ =>
    dsimp only [RawTree.isCanon] at h
    exact bool_and_left h

/-- Right child of a canonical `.node` is canonical. -/
theorem rawTree_isCanon_right {α : Type} {l r : RawTree α} {v : Option α}
    (h : (RawTree.node l v r).isCanon = true) : r.isCanon = true := by
  cases v with
  | none =>
    dsimp only [RawTree.isCanon] at h
    exact bool_and_right h
  | some _ =>
    dsimp only [RawTree.isCanon] at h
    exact bool_and_right h

/-- Smart constructor collapsing `.node .leaf none .leaf` to `.leaf`. -/
def RawTree.make {α : Type} (l : RawTree α) (v : Option α) (r : RawTree α) :
    RawTree α :=
  match v with
  | some x => .node l (some x) r
  | none =>
    match l with
    | .leaf =>
      match r with
      | .leaf => .leaf
      | .node rl rv rr => .node .leaf none (.node rl rv rr)
    | .node ll lv lr => .node (.node ll lv lr) none r

/-- `RawTree.make` preserves canonicality when both children are canonical. -/
theorem rawTree_make_isCanon {α : Type} {l r : RawTree α} (v : Option α)
    (hl : l.isCanon = true) (hr : r.isCanon = true) :
    (RawTree.make l v r).isCanon = true := by
  cases v with
  | some _ =>
    dsimp only [RawTree.make, RawTree.isCanon]
    rw [hl, hr]
    rfl
  | none =>
    cases l with
    | leaf =>
      cases r with
      | leaf => rfl
      | node _ _ _ =>
        dsimp only [RawTree.make, RawTree.isCanon, RawTree.isLeaf] at hl hr
        dsimp only [RawTree.make, RawTree.isCanon, RawTree.isLeaf]
        rw [hr]
        rfl
    | node _ _ _ =>
      dsimp only [RawTree.make, RawTree.isCanon, RawTree.isLeaf] at hl hr
      dsimp only [RawTree.make, RawTree.isCanon, RawTree.isLeaf]
      rw [hl, hr]
      rfl

/-- Look up key `k` in `RawTree`. -/
noncomputable def RawTree.get {α : Type} : RawTree α → Pos → Option α
  | .leaf, _ => none
  | .node l v r, k =>
    match k with
    | .xH => v
    | .xO k' => RawTree.get l k'
    | .xI k' => RawTree.get r k'

/-- Lookup through `RawTree.make l v r` agrees with `.node l v r`. -/
theorem rawTree_get_make {α : Type} (l : RawTree α) (v : Option α)
    (r : RawTree α) (k : Pos) :
    RawTree.get (RawTree.make l v r) k = RawTree.get (.node l v r) k := by
  cases v with
  | some _ => rfl
  | none =>
    cases l with
    | leaf =>
      cases r with
      | leaf => cases k <;> rfl
      | node _ _ _ => rfl
    | node _ _ _ => rfl

/-- Insert or overwrite key `k` with `x` in `RawTree`. -/
noncomputable def RawTree.set {α : Type} : RawTree α → Pos → α → RawTree α
  | .leaf, .xH, x => .node .leaf (some x) .leaf
  | .leaf, .xO k', x => RawTree.make (RawTree.set .leaf k' x) none .leaf
  | .leaf, .xI k', x => RawTree.make .leaf none (RawTree.set .leaf k' x)
  | .node l _ r, .xH, x => .node l (some x) r
  | .node l v r, .xO k', x => RawTree.make (RawTree.set l k' x) v r
  | .node l v r, .xI k', x => RawTree.make l v (RawTree.set r k' x)

/-- `RawTree.set` preserves canonicality. -/
theorem rawTree_set_isCanon {α : Type} :
    ∀ (t : RawTree α) (k : Pos) (x : α),
      t.isCanon = true → (RawTree.set t k x).isCanon = true
  | .leaf, .xH, _, _ => rfl
  | .leaf, .xO k', x, _ =>
    rawTree_make_isCanon none (rawTree_set_isCanon .leaf k' x rfl) rfl
  | .leaf, .xI k', x, _ =>
    rawTree_make_isCanon none rfl (rawTree_set_isCanon .leaf k' x rfl)
  | .node l _ r, .xH, _, h => by
    dsimp only [RawTree.set, RawTree.isCanon]
    rw [rawTree_isCanon_left h, rawTree_isCanon_right h]
    rfl
  | .node l v r, .xO k', x, h =>
    rawTree_make_isCanon v
      (rawTree_set_isCanon l k' x (rawTree_isCanon_left h))
      (rawTree_isCanon_right h)
  | .node l v r, .xI k', x, h =>
    rawTree_make_isCanon v
      (rawTree_isCanon_left h)
      (rawTree_set_isCanon r k' x (rawTree_isCanon_right h))

/-- Look-up after `RawTree.set` at the same key returns `some x`. -/
theorem rawTree_get_set_same {α : Type} :
    ∀ (t : RawTree α) (k : Pos) (x : α),
      RawTree.get (RawTree.set t k x) k = some x
  | .leaf, .xH, _ => rfl
  | .leaf, .xO k', x => by
    dsimp only [RawTree.set]
    rw [rawTree_get_make]
    exact rawTree_get_set_same .leaf k' x
  | .leaf, .xI k', x => by
    dsimp only [RawTree.set]
    rw [rawTree_get_make]
    exact rawTree_get_set_same .leaf k' x
  | .node _ _ _, .xH, _ => rfl
  | .node l _ _, .xO k', x => by
    dsimp only [RawTree.set]
    rw [rawTree_get_make]
    exact rawTree_get_set_same l k' x
  | .node _ _ r, .xI k', x => by
    dsimp only [RawTree.set]
    rw [rawTree_get_make]
    exact rawTree_get_set_same r k' x

/-- Look-up after `RawTree.set` at a distinct key leaves the old value
unchanged. -/
theorem rawTree_get_set_other {α : Type} :
    ∀ (t : RawTree α) (k1 k2 : Pos) (x : α),
      k1 ≠ k2 → RawTree.get (RawTree.set t k1 x) k2 = RawTree.get t k2
  | .leaf, .xH, .xH, _, hNe => False.elim (hNe rfl)
  | .leaf, .xH, .xO _, _, _ => rfl
  | .leaf, .xH, .xI _, _, _ => rfl
  | .leaf, .xO _, .xH, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .leaf, .xO k1', .xO k2', x, hNe => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]
    exact rawTree_get_set_other .leaf k1' k2' x
      (fun h => hNe (congrArg Pos.xO h))
  | .leaf, .xO _, .xI _, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .leaf, .xI _, .xH, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .leaf, .xI _, .xO _, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .leaf, .xI k1', .xI k2', x, hNe => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]
    exact rawTree_get_set_other .leaf k1' k2' x
      (fun h => hNe (congrArg Pos.xI h))
  | .node _ _ _, .xH, .xH, _, hNe => False.elim (hNe rfl)
  | .node _ _ _, .xH, .xO _, _, _ => rfl
  | .node _ _ _, .xH, .xI _, _, _ => rfl
  | .node _ _ _, .xO _, .xH, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .node l _ _, .xO k1', .xO k2', x, hNe => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]
    exact rawTree_get_set_other l k1' k2' x (fun h => hNe (congrArg Pos.xO h))
  | .node _ _ _, .xO _, .xI _, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .node _ _ _, .xI _, .xH, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .node _ _ _, .xI _, .xO _, _, _ => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]; rfl
  | .node _ _ r, .xI k1', .xI k2', x, hNe => by
    dsimp only [RawTree.set]; rw [rawTree_get_make]
    exact rawTree_get_set_other r k1' k2' x (fun h => hNe (congrArg Pos.xI h))

/-- Remove key `k` from `RawTree`, re-normalizing empty branches. -/
noncomputable def RawTree.remove {α : Type} : RawTree α → Pos → RawTree α
  | .leaf, _ => .leaf
  | .node l _ r, .xH => RawTree.make l none r
  | .node l v r, .xO k' => RawTree.make (RawTree.remove l k') v r
  | .node l v r, .xI k' => RawTree.make l v (RawTree.remove r k')

/-- `RawTree.remove` preserves canonicality. -/
theorem rawTree_remove_isCanon {α : Type} :
    ∀ (t : RawTree α) (k : Pos),
      t.isCanon = true → (RawTree.remove t k).isCanon = true
  | .leaf, _, _ => rfl
  | .node _ _ _, .xH, h =>
    rawTree_make_isCanon none (rawTree_isCanon_left h) (rawTree_isCanon_right h)
  | .node l v _, .xO k', h =>
    rawTree_make_isCanon v
      (rawTree_remove_isCanon l k' (rawTree_isCanon_left h))
      (rawTree_isCanon_right h)
  | .node _ v r, .xI k', h =>
    rawTree_make_isCanon v
      (rawTree_isCanon_left h)
      (rawTree_remove_isCanon r k' (rawTree_isCanon_right h))

/-- Look-up after `RawTree.remove` at the removed key returns `none`. -/
theorem rawTree_get_remove_same {α : Type} :
    ∀ (t : RawTree α) (k : Pos), RawTree.get (RawTree.remove t k) k = none
  | .leaf, _ => rfl
  | .node _ _ _, .xH => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node l _ _, .xO k' => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]
    exact rawTree_get_remove_same l k'
  | .node _ _ r, .xI k' => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]
    exact rawTree_get_remove_same r k'

/-- Look-up after `RawTree.remove` at a distinct key is unchanged. -/
theorem rawTree_get_remove_other {α : Type} :
    ∀ (t : RawTree α) (k1 k2 : Pos),
      k1 ≠ k2 → RawTree.get (RawTree.remove t k1) k2 = RawTree.get t k2
  | .leaf, _, _, _ => rfl
  | .node _ _ _, .xH, .xH, hNe => False.elim (hNe rfl)
  | .node _ _ _, .xH, .xO _, _ => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node _ _ _, .xH, .xI _, _ => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node _ _ _, .xO _, .xH, _ => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node l _ _, .xO k1', .xO k2', hNe => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]
    exact rawTree_get_remove_other l k1' k2' (fun h => hNe (congrArg Pos.xO h))
  | .node _ _ _, .xO _, .xI _, _ => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node _ _ _, .xI _, .xH, _ => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node _ _ _, .xI _, .xO _, _ => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]; rfl
  | .node _ _ r, .xI k1', .xI k2', hNe => by
    dsimp only [RawTree.remove]; rw [rawTree_get_make]
    exact rawTree_get_remove_other r k1' k2' (fun h => hNe (congrArg Pos.xI h))

/-- Canonical `RawTree` whose lookups are everywhere `none` must be `.leaf`. -/
theorem rawTree_all_none_eq_leaf {α : Type} :
    ∀ (t : RawTree α),
      t.isCanon = true → (∀ k : Pos, RawTree.get t k = none) → t = .leaf
  | .leaf, _, _ => rfl
  | .node l v r, hCanon, hNone => by
    have hv : v = none := hNone .xH
    cases hv
    have hl : l = .leaf :=
      rawTree_all_none_eq_leaf l (rawTree_isCanon_left hCanon)
        (fun k => hNone (.xO k))
    have hr : r = .leaf :=
      rawTree_all_none_eq_leaf r (rawTree_isCanon_right hCanon)
        (fun k => hNone (.xI k))
    rw [hl, hr] at hCanon
    dsimp only [RawTree.isCanon, RawTree.isLeaf] at hCanon
    nomatch hCanon

/-- Two canonical `RawTree`s with identical pointwise lookups are equal. -/
theorem rawTree_eq_of_get {α : Type} :
    ∀ (t1 t2 : RawTree α),
      t1.isCanon = true → t2.isCanon = true →
      (∀ k : Pos, RawTree.get t1 k = RawTree.get t2 k) → t1 = t2
  | .leaf, t2, _, hc2, hGet =>
    (rawTree_all_none_eq_leaf t2 hc2 (fun k => (hGet k).symm)).symm
  | .node l1 v1 r1, .leaf, hc1, _, hGet =>
    rawTree_all_none_eq_leaf (.node l1 v1 r1) hc1 hGet
  | .node l1 v1 r1, .node l2 v2 r2, hc1, hc2, hGet => by
    have hv : v1 = v2 := hGet .xH
    have hl : l1 = l2 :=
      rawTree_eq_of_get l1 l2 (rawTree_isCanon_left hc1)
        (rawTree_isCanon_left hc2) (fun k => hGet (.xO k))
    have hr : r1 = r2 :=
      rawTree_eq_of_get r1 r2 (rawTree_isCanon_right hc1)
        (rawTree_isCanon_right hc2) (fun k => hGet (.xI k))
    rw [hl, hv, hr]

/-- Canonical positive binary radix trie invariant bundle (`raw` paired with its
`raw.isCanon = true` proof). -/
structure PTree (α : Type) where
  raw   : RawTree α
  canon : raw.isCanon = true

/-- Equality of underlying `raw` fields implies equality of `PTree`s by proof
irrelevance on `canon`. -/
theorem ptree_mk_eq {α : Type} {r1 r2 : RawTree α}
    {h1 : r1.isCanon = true} {h2 : r2.isCanon = true}
    (hEq : r1 = r2) : PTree.mk r1 h1 = PTree.mk r2 h2 := by
  cases hEq
  rfl

/-- Empty canonical trie. -/
def PTree.empty {α : Type} : PTree α :=
  ⟨.leaf, rfl⟩

/-- Look up key `k` in canonical trie `t`. -/
noncomputable def PTree.get {α : Type} (t : PTree α) (k : Pos) : Option α :=
  RawTree.get t.raw k

/-- Insert or update key `k` with value `v` in canonical trie `t`. -/
noncomputable def PTree.set {α : Type} (t : PTree α) (k : Pos) (v : α) :
    PTree α :=
  ⟨RawTree.set t.raw k v, rawTree_set_isCanon t.raw k v t.canon⟩

/-- Remove key `k` from canonical trie `t`. -/
noncomputable def PTree.remove {α : Type} (t : PTree α) (k : Pos) : PTree α :=
  ⟨RawTree.remove t.raw k, rawTree_remove_isCanon t.raw k t.canon⟩

/-- Single-entry canonical trie mapping `k` to `v`. -/
noncomputable def PTree.singleton {α : Type} (k : Pos) (v : α) : PTree α :=
  PTree.set PTree.empty k v

/-- Axiom-free extensional equality for `PTree`: two canonical tries with
identical pointwise `get` lookups are equal. -/
theorem ptree_eq_of_get {α : Type} (t1 t2 : PTree α)
    (hGet : ∀ k : Pos, t1.get k = t2.get k) : t1 = t2 := by
  cases t1 with
  | mk r1 c1 =>
    cases t2 with
    | mk r2 c2 =>
      exact ptree_mk_eq (rawTree_eq_of_get r1 r2 c1 c2 hGet)

/-- `PTree.empty` returns `none` at every key. -/
theorem ptree_get_empty {α : Type} (k : Pos) :
    (PTree.empty : PTree α).get k = none := rfl

/-- Lookup on `(t.set k v)` at `k` returns `some v`. -/
theorem ptree_get_set_same {α : Type} (t : PTree α) (k : Pos) (v : α) :
    (t.set k v).get k = some v :=
  rawTree_get_set_same t.raw k v

/-- Lookup on `(t.set k1 v)` at `k2 ≠ k1` equals `t.get k2`. -/
theorem ptree_get_set_other {α : Type} (t : PTree α) (k1 k2 : Pos) (v : α)
    (hNe : k1 ≠ k2) : (t.set k1 v).get k2 = t.get k2 :=
  rawTree_get_set_other t.raw k1 k2 v hNe

/-- Lookup on `(t.remove k)` at `k` returns `none`. -/
theorem ptree_get_remove_same {α : Type} (t : PTree α) (k : Pos) :
    (t.remove k).get k = none :=
  rawTree_get_remove_same t.raw k

/-- Lookup on `(t.remove k1)` at `k2 ≠ k1` equals `t.get k2`. -/
theorem ptree_get_remove_other {α : Type} (t : PTree α) (k1 k2 : Pos)
    (hNe : k1 ≠ k2) : (t.remove k1).get k2 = t.get k2 :=
  rawTree_get_remove_other t.raw k1 k2 hNe

/-- Distinct-key `PTree.set` updates commute structurally. -/
theorem ptree_set_set_comm {α : Type} (t : PTree α) {k1 k2 : Pos} (v1 v2 : α)
    (hNe : k1 ≠ k2) :
    (t.set k1 v1).set k2 v2 = (t.set k2 v2).set k1 v1 := by
  apply ptree_eq_of_get
  intro q
  cases h1 : Pos.beq k1 q with
  | true =>
    have hq1 := pos_eq_of_beq h1
    rw [← hq1]
    rw [ptree_get_set_other _ _ _ _ hNe.symm, ptree_get_set_same,
        ptree_get_set_same]
  | false =>
    have hNe1 : k1 ≠ q := fun h => by rw [h, posBeq_refl] at h1; nomatch h1
    cases h2 : Pos.beq k2 q with
    | true =>
      have hq2 := pos_eq_of_beq h2
      rw [← hq2]
      rw [ptree_get_set_same, ptree_get_set_other _ _ _ _ hNe,
          ptree_get_set_same]
    | false =>
      have hNe2 : k2 ≠ q := fun h => by rw [h, posBeq_refl] at h2; nomatch h2
      rw [ptree_get_set_other _ _ _ _ hNe2, ptree_get_set_other _ _ _ _ hNe1]
      rw [ptree_get_set_other _ _ _ _ hNe1, ptree_get_set_other _ _ _ _ hNe2]

/-! ## 3. Union, Disjointness, and Polymorphic `diffWith` Heap Framing -/

/-- Pointwise domain disjointness of two `PTree` maps. -/
def PTree.DisjointProp {α : Type} (a b : PTree α) : Prop :=
  ∀ k : Pos, a.get k = none ∨ b.get k = none

/-- Left-biased union on `RawTree`, preserving canonicality via `make`. -/
noncomputable def RawTree.union {α : Type} : RawTree α → RawTree α → RawTree α
  | .leaf, b => b
  | a, .leaf => a
  | .node l1 v1 r1, .node l2 v2 r2 =>
    let v := match v1 with | some x => some x | none => v2
    RawTree.make (RawTree.union l1 l2) v (RawTree.union r1 r2)

/-- `RawTree.union` preserves canonicality. -/
theorem rawTree_union_isCanon {α : Type} :
    ∀ (a b : RawTree α),
      a.isCanon = true → b.isCanon = true → (RawTree.union a b).isCanon = true
  | .leaf, _, _, hb => hb
  | .node _ _ _, .leaf, ha, _ => ha
  | .node l1 _ r1, .node l2 _ r2, ha, hb =>
    rawTree_make_isCanon _
      (rawTree_union_isCanon l1 l2 (rawTree_isCanon_left ha)
        (rawTree_isCanon_left hb))
      (rawTree_union_isCanon r1 r2 (rawTree_isCanon_right ha)
        (rawTree_isCanon_right hb))

/-- Left-biased union of two canonical tries. -/
noncomputable def PTree.union {α : Type} (a b : PTree α) : PTree α :=
  ⟨RawTree.union a.raw b.raw, rawTree_union_isCanon a.raw b.raw a.canon b.canon⟩

/-- Pointwise lookup behavior of `RawTree.union`. -/
theorem rawTree_get_union {α : Type} :
    ∀ (a b : RawTree α) (k : Pos),
      RawTree.get (RawTree.union a b) k =
        match RawTree.get a k with
        | some x => some x
        | none => RawTree.get b k
  | .leaf, _, _ => rfl
  | .node _ _ _, .leaf, k => by
    dsimp only [RawTree.union]
    cases RawTree.get (.node _ _ _) k <;> rfl
  | .node l1 _ r1, .node l2 _ r2, k => by
    dsimp only [RawTree.union]
    rw [rawTree_get_make]
    cases k with
    | xH => rfl
    | xO k' => exact rawTree_get_union l1 l2 k'
    | xI k' => exact rawTree_get_union r1 r2 k'

/-- Pointwise lookup behavior of `PTree.union`. -/
theorem ptree_get_union {α : Type} (a b : PTree α) (k : Pos) :
    (PTree.union a b).get k =
      match a.get k with
      | some x => some x
      | none => b.get k :=
  rawTree_get_union a.raw b.raw k

/-- Empty left identity for `PTree.union`. -/
theorem ptree_union_empty_left {α : Type} (t : PTree α) :
    PTree.union PTree.empty t = t :=
  ptree_mk_eq rfl

/-- Empty right identity for `PTree.union`. -/
theorem ptree_union_empty_right {α : Type} (t : PTree α) :
    PTree.union t PTree.empty = t := by
  apply ptree_eq_of_get
  intro k
  rw [ptree_get_union]
  cases t.get k <;> rfl

/-- Disjoint `PTree.union` commutes. -/
theorem ptree_union_comm_of_disjoint {α : Type} {a b : PTree α}
    (hDisj : PTree.DisjointProp a b) :
    PTree.union a b = PTree.union b a := by
  apply ptree_eq_of_get
  intro k
  rw [ptree_get_union, ptree_get_union]
  cases hDisj k with
  | inl ha =>
    rw [ha]
    cases hb : b.get k <;> rfl
  | inr hb =>
    rw [hb]
    cases ha : a.get k <;> rfl

/-- Structural recursion helper for `RawTree.diffWith` (`req` first so `req`
decreases structurally alongside `goal`). -/
noncomputable def RawTree.diffWithLoop {α : Type} (eqB : α → α → Bool) :
    RawTree α → RawTree α → Option (RawTree α)
  | .leaf, goal => some goal
  | .node _ _ _, .leaf => none
  | .node rl rv rr, .node gl gv gr =>
    let ov : Option (Option α) :=
      match rv, gv with
      | none, _ => some gv
      | some r, some g =>
        match eqB g r with
        | true => some none
        | false => none
      | some _, none => none
    match ov with
    | none => none
    | some v' =>
      match RawTree.diffWithLoop eqB rl gl with
      | none => none
      | some l' =>
        match RawTree.diffWithLoop eqB rr gr with
        | none => none
        | some r' => some (RawTree.make l' v' r')

/-- Subtract required entries `req` from `goal` using equality predicate
`eqB`, returning `some rem` on match or `none` if any `req` entry is missing or
disagrees. -/
noncomputable def RawTree.diffWith {α : Type} (eqB : α → α → Bool)
    (goal req : RawTree α) : Option (RawTree α) :=
  RawTree.diffWithLoop eqB req goal

/-- `RawTree.diffWith` produces a canonical remainder whenever `goal` is
canonical. -/
theorem rawTree_diffWith_isCanon {α : Type} (eqB : α → α → Bool) :
    ∀ (goal req rem : RawTree α),
      goal.isCanon = true →
      RawTree.diffWith eqB goal req = some rem →
      rem.isCanon = true
  | goal, .leaf, rem, hg, hDiff => by
    injection hDiff with hEq
    rw [← hEq]
    exact hg
  | .leaf, .node _ _ _, _, _, hDiff => by
    nomatch hDiff
  | .node gl gv gr, .node rl rv rr, rem, hg, hDiff => by
    dsimp only [RawTree.diffWith, RawTree.diffWithLoop] at hDiff
    cases hOv :
      (match rv, gv with
       | none, _ => some gv
       | some r, some g =>
         match eqB g r with
         | true => some none
         | false => none
       | some _, none => none) with
    | none => rw [hOv] at hDiff; nomatch hDiff
    | some v' =>
      rw [hOv] at hDiff
      dsimp only at hDiff
      cases hL : RawTree.diffWithLoop eqB rl gl with
      | none => rw [hL] at hDiff; nomatch hDiff
      | some l' =>
        rw [hL] at hDiff
        dsimp only at hDiff
        cases hR : RawTree.diffWithLoop eqB rr gr with
        | none => rw [hR] at hDiff; nomatch hDiff
        | some r' =>
          rw [hR] at hDiff
          dsimp only at hDiff
          injection hDiff with hEq
          rw [← hEq]
          exact rawTree_make_isCanon v'
            (rawTree_diffWith_isCanon eqB gl rl l'
              (rawTree_isCanon_left hg) hL)
            (rawTree_diffWith_isCanon eqB gr rr r'
              (rawTree_isCanon_right hg) hR)

/-- Package a `some` result from `RawTree.diffWith` with its canonicality proof
into `Option (PTree α)`. -/
def ptreeWrapDiff {α : Type} (eqB : α → α → Bool) (goal req : RawTree α)
    (hg : goal.isCanon = true) (opt : Option (RawTree α))
    (h : RawTree.diffWith eqB goal req = opt) : Option (PTree α) :=
  match opt, h with
  | none, _ => none
  | some rem, h => some ⟨rem, rawTree_diffWith_isCanon eqB goal req rem hg h⟩

/-- Recover the underlying `RawTree.diffWith = some rem.raw` witness when
`ptreeWrapDiff` returns `some rem`. -/
theorem ptreeWrapDiff_some {α : Type} {eqB : α → α → Bool}
    {goal req : RawTree α} {hg : goal.isCanon = true}
    {opt : Option (RawTree α)} {h : RawTree.diffWith eqB goal req = opt}
    {rem : PTree α}
    (hEq : ptreeWrapDiff eqB goal req hg opt h = some rem) :
    opt = some rem.raw := by
  cases opt with
  | none => nomatch hEq
  | some _ =>
    dsimp only [ptreeWrapDiff] at hEq
    injection hEq with hMk
    rw [← hMk]

/-- Deterministic structural trie subtraction `PTree.diffWith eqB goal req`
(single non-backtracking pass over `req`). -/
noncomputable def PTree.diffWith {α : Type} (eqB : α → α → Bool)
    (goal req : PTree α) : Option (PTree α) :=
  ptreeWrapDiff eqB goal.raw req.raw goal.canon
    (RawTree.diffWith eqB goal.raw req.raw) rfl

/-- Pointwise invariant of `RawTree.diffWith` when `eqB` is sound. -/
theorem rawTree_diffWith_pointwise {α : Type} (eqB : α → α → Bool)
    (hSoundEq : ∀ {x y : α}, eqB x y = true → x = y) :
    ∀ (goal req rem : RawTree α),
      RawTree.diffWith eqB goal req = some rem →
      ∀ k : Pos,
        (RawTree.get req k = none ∧ RawTree.get rem k = RawTree.get goal k) ∨
        (∃ x : α, RawTree.get req k = some x ∧ RawTree.get goal k = some x ∧
          RawTree.get rem k = none)
  | _, .leaf, rem, hDiff, _ => by
    injection hDiff with hEq
    rw [← hEq]
    exact Or.inl ⟨rfl, rfl⟩
  | .leaf, .node _ _ _, _, hDiff, _ => by
    nomatch hDiff
  | .node gl gv gr, .node rl rv rr, rem, hDiff, k => by
    dsimp only [RawTree.diffWith, RawTree.diffWithLoop] at hDiff
    cases hOv :
      (match rv, gv with
       | none, _ => some gv
       | some r, some g =>
         match eqB g r with
         | true => some none
         | false => none
       | some _, none => none) with
    | none => rw [hOv] at hDiff; nomatch hDiff
    | some v' =>
      rw [hOv] at hDiff
      dsimp only at hDiff
      cases hL : RawTree.diffWithLoop eqB rl gl with
      | none => rw [hL] at hDiff; nomatch hDiff
      | some l' =>
        rw [hL] at hDiff
        dsimp only at hDiff
        cases hR : RawTree.diffWithLoop eqB rr gr with
        | none => rw [hR] at hDiff; nomatch hDiff
        | some r' =>
          rw [hR] at hDiff
          dsimp only at hDiff
          injection hDiff with hEq
          rw [← hEq]
          cases k with
          | xH =>
            dsimp only [RawTree.get]
            rw [rawTree_get_make]
            dsimp only [RawTree.get]
            cases rv with
            | none =>
              dsimp only at hOv
              injection hOv with hv'
              rw [hv']
              exact Or.inl ⟨rfl, rfl⟩
            | some r =>
              cases gv with
              | none => dsimp only at hOv; nomatch hOv
              | some g =>
                dsimp only at hOv
                cases hBeq : eqB g r with
                | false => rw [hBeq] at hOv; nomatch hOv
                | true =>
                  rw [hBeq] at hOv
                  injection hOv with hv'
                  have hgr : g = r := hSoundEq hBeq
                  rw [← hv', hgr]
                  exact Or.inr ⟨r, rfl, rfl, rfl⟩
          | xO k' =>
            dsimp only [RawTree.get]
            rw [rawTree_get_make]
            exact rawTree_diffWith_pointwise eqB hSoundEq gl rl l' hL k'
          | xI k' =>
            dsimp only [RawTree.get]
            rw [rawTree_get_make]
            exact rawTree_diffWith_pointwise eqB hSoundEq gr rr r' hR k'

/-- Deterministic separation-logic framing: whenever `PTree.diffWith eqB goal
req = some rem`, `req` and `rem` are disjoint and
`PTree.union req rem = goal`. -/
theorem ptree_diffWith_sound {α : Type} (eqB : α → α → Bool)
    (hSoundEq : ∀ {x y : α}, eqB x y = true → x = y)
    {goal req rem : PTree α}
    (hDiff : PTree.diffWith eqB goal req = some rem) :
    PTree.DisjointProp req rem ∧ PTree.union req rem = goal := by
  have hRaw : RawTree.diffWith eqB goal.raw req.raw = some rem.raw :=
    ptreeWrapDiff_some hDiff
  have hPw := rawTree_diffWith_pointwise eqB hSoundEq goal.raw req.raw rem.raw
    hRaw
  refine ⟨?_, ?_⟩
  · intro k
    cases hPw k with
    | inl h => exact Or.inl h.1
    | inr h =>
      cases h with
      | intro _ hx => exact Or.inr hx.2.2
  · apply ptree_eq_of_get
    intro k
    dsimp only [PTree.get, PTree.union]
    rw [rawTree_get_union]
    cases hPw k with
    | inl h => rw [h.1, h.2]
    | inr h =>
      cases h with
      | intro _ hx => rw [hx.1, hx.2.1]

/-- Removing key `k` from `PTree.singleton k v` yields `PTree.empty`. -/
theorem ptree_remove_singleton {α : Type} (k : Pos) (v : α) :
    (PTree.singleton k v).remove k = PTree.empty := by
  apply ptree_eq_of_get
  intro q
  cases hBeq : Pos.beq k q with
  | true =>
    rw [← pos_eq_of_beq hBeq]
    exact ptree_get_remove_same _ _
  | false =>
    have hNe : k ≠ q := fun h => by rw [h, posBeq_refl] at hBeq; nomatch hBeq
    rw [ptree_get_remove_other _ _ _ hNe]
    exact ptree_get_set_other _ _ _ _ hNe

/-- Subtracting `PTree.empty` from `goal` returns `some goal`. -/
theorem ptree_diffWith_empty_req {α : Type} (eqB : α → α → Bool)
    (goal : PTree α) :
    PTree.diffWith eqB goal PTree.empty = some goal := rfl

/-! ## 4. Top-Down Strided Tabulation (`ptreeTabulate`) -/

/-- Bit length (`≥ 1`) of a positive binary key `Pos` (specification helper). -/
noncomputable def posDepth : Pos → Nat
  | .xH => 1
  | .xO p => posDepth p + 1
  | .xI p => posDepth p + 1

/-- Computable `2^n` via `@Nat.rec` (`0` `noncomputable`). -/
def ptreePow2 (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => 2 * ih) n

private theorem posToNat_pos : ∀ k : Pos, 0 < posToNat k
  | .xH => Nat.zero_lt_one
  | .xO p => Nat.mul_pos (Nat.succ_pos 1) (posToNat_pos p)
  | .xI p => Nat.succ_pos (2 * posToNat p)

private theorem ptreePow2_pos (n : Nat) : 0 < ptreePow2 n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ _ ih => exact Nat.mul_pos (Nat.succ_pos 1) ih

/-- Bit-depth characterization: `posDepth k ≤ d ↔ posToNat k < ptreePow2 d`. -/
theorem posDepth_le_iff_lt_pow2 :
    ∀ (k : Pos) (d : Nat), posDepth k ≤ d ↔ posToNat k < ptreePow2 d
  | .xH, 0 =>
    ⟨fun h => False.elim (Nat.not_succ_le_zero 0 h),
     fun h => False.elim (Nat.lt_irrefl 1 h)⟩
  | .xH, d' + 1 =>
    ⟨fun _ => by
       change 1 < 2 * ptreePow2 d'
       have hPos : 1 ≤ ptreePow2 d' := ptreePow2_pos d'
       have h2 : 2 * 1 ≤ 2 * ptreePow2 d' := Nat.mul_le_mul_left 2 hPos
       exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h2,
     fun _ => Nat.succ_le_succ (Nat.zero_le d')⟩
  | .xO p, 0 =>
    ⟨fun h => False.elim (Nat.not_succ_le_zero (posDepth p) h),
     fun h => by
       have hp : 1 ≤ posToNat p := posToNat_pos p
       have h2 : 2 ≤ 2 * posToNat p := Nat.mul_le_mul_left 2 hp
       exact False.elim (Nat.not_lt_of_ge h2 (Nat.lt_trans h (Nat.lt_succ_self 1)))⟩
  | .xO p, d' + 1 => by
    have ih := posDepth_le_iff_lt_pow2 p d'
    constructor
    · intro h
      have hLt : posToNat p < ptreePow2 d' := ih.mp (Nat.le_of_succ_le_succ h)
      change 2 * posToNat p < 2 * ptreePow2 d'
      have hSucc : posToNat p + 1 ≤ ptreePow2 d' := hLt
      have hMul := Nat.mul_le_mul_left 2 hSucc
      rw [Nat.mul_succ] at hMul
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) hMul
    · intro h
      change 2 * posToNat p < 2 * ptreePow2 d' at h
      have hLt : posToNat p < ptreePow2 d' := by
        cases Nat.lt_or_ge (posToNat p) (ptreePow2 d') with
        | inl hl => exact hl
        | inr hg =>
          exact False.elim
            (Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hg) h)
      exact Nat.succ_le_succ (ih.mpr hLt)
  | .xI p, 0 =>
    ⟨fun h => False.elim (Nat.not_succ_le_zero (posDepth p) h),
     fun h => by
       have hp : 1 ≤ posToNat p := posToNat_pos p
       have h2 : 2 ≤ 2 * posToNat p := Nat.mul_le_mul_left 2 hp
       have h3 : 3 ≤ 2 * posToNat p + 1 := Nat.succ_le_succ h2
       exact False.elim
         (Nat.not_lt_of_ge h3 (Nat.lt_trans h (Nat.lt_succ_of_lt (Nat.lt_succ_self 1))))⟩
  | .xI p, d' + 1 => by
    have ih := posDepth_le_iff_lt_pow2 p d'
    constructor
    · intro h
      have hLt : posToNat p < ptreePow2 d' := ih.mp (Nat.le_of_succ_le_succ h)
      change 2 * posToNat p + 1 < 2 * ptreePow2 d'
      have hSucc : posToNat p + 1 ≤ ptreePow2 d' := hLt
      have hMul := Nat.mul_le_mul_left 2 hSucc
      rw [Nat.mul_succ] at hMul
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hMul
    · intro h
      change 2 * posToNat p + 1 < 2 * ptreePow2 d' at h
      have hLt : posToNat p < ptreePow2 d' := by
        cases Nat.lt_or_ge (posToNat p) (ptreePow2 d') with
        | inl hl => exact hl
        | inr hg =>
          have h2 := Nat.mul_le_mul_left 2 hg
          exact False.elim
            (Nat.not_lt_of_ge (Nat.le_trans h2 (Nat.le_succ _)) h)
      exact Nat.succ_le_succ (ih.mpr hLt)

/-- Top-down strided builder for canonical `RawTree α` over `Nat` indices
`0 .. 2^depth - 2` (encoded via `natToPos n`, whose `posToNat` value is
`n + 1`).

Why top-down tabulation: building an `N`-entry CFG table with sequential
`List.foldl PTree.set` forces all `N` insertions on the very first lookup and
can exceed `maxRecDepth = 512` at large `N`. Because `RawTree.make l (some x) r`
returns `.node l (some x) r` without forcing `l` or `r`, top-down tabulation
forces only the `O(log N)` nodes along a queried key's path during WHNF
reduction. -/
def RawTree.tabulateGo {α : Type} (depth : Nat) :
    Nat → Nat → (Nat → Option α) → RawTree α :=
  @Nat.rec (fun _ => Nat → Nat → (Nat → Option α) → RawTree α)
    (fun _ _ _ => .leaf)
    (fun _ ih base stride f =>
      RawTree.make
        (ih base (2 * stride) f)
        (f (base + stride - 1))
        (ih (base + stride) (2 * stride) f))
    depth

/-- `RawTree.tabulateGo` always produces a canonical `RawTree α`. -/
theorem rawTree_tabulateGo_isCanon {α : Type} :
    ∀ (depth base stride : Nat) (f : Nat → Option α),
      (RawTree.tabulateGo depth base stride f).isCanon = true
  | 0, _, _, _ => rfl
  | d + 1, base, stride, f =>
    rawTree_make_isCanon (f (base + stride - 1))
      (rawTree_tabulateGo_isCanon d base (2 * stride) f)
      (rawTree_tabulateGo_isCanon d (base + stride) (2 * stride) f)

/-- Top-down strided canonical `PTree α` tabulation covering all `k : Pos` with
`posDepth k ≤ depth` (i.e., `natToPos n` for all `n + 1 < ptreePow2 depth`). -/
def ptreeTabulate {α : Type} (depth : Nat) (f : Nat → Option α) : PTree α :=
  ⟨RawTree.tabulateGo depth 0 1 f, rawTree_tabulateGo_isCanon depth 0 1 f⟩

/-- Method alias for `ptreeTabulate`. -/
abbrev PTree.tabulate {α : Type} (depth : Nat) (f : Nat → Option α) : PTree α :=
  ptreeTabulate depth f

/-- In-bounds lookup law for `RawTree.tabulateGo` (`posDepth k ≤ depth`). -/
theorem rawTree_get_tabulateGo_in {α : Type} :
    ∀ (depth base stride : Nat) (f : Nat → Option α) (k : Pos),
      posDepth k ≤ depth →
      RawTree.get (RawTree.tabulateGo depth base stride f) k =
        f (base + stride * posToNat k - 1)
  | 0, _, _, _, k, hk => by
    cases k with
    | xH => exact False.elim (Nat.not_succ_le_zero 0 hk)
    | xO p => exact False.elim (Nat.not_succ_le_zero (posDepth p) hk)
    | xI p => exact False.elim (Nat.not_succ_le_zero (posDepth p) hk)
  | d + 1, base, stride, f, k, hk => by
    change RawTree.get
        (RawTree.make
          (RawTree.tabulateGo d base (2 * stride) f)
          (f (base + stride - 1))
          (RawTree.tabulateGo d (base + stride) (2 * stride) f)) k =
      f (base + stride * posToNat k - 1)
    rw [rawTree_get_make]
    cases k with
    | xH =>
      change f (base + stride - 1) = f (base + stride * 1 - 1)
      rw [Nat.mul_one]
    | xO p =>
      change RawTree.get (RawTree.tabulateGo d base (2 * stride) f) p =
        f (base + stride * (2 * posToNat p) - 1)
      rw [rawTree_get_tabulateGo_in d base (2 * stride) f p
            (Nat.le_of_succ_le_succ hk),
          Nat.mul_comm 2 stride, Nat.mul_assoc stride 2 (posToNat p)]
    | xI p =>
      change RawTree.get
          (RawTree.tabulateGo d (base + stride) (2 * stride) f) p =
        f (base + stride * (2 * posToNat p + 1) - 1)
      rw [rawTree_get_tabulateGo_in d (base + stride) (2 * stride) f p
            (Nat.le_of_succ_le_succ hk)]
      have harith :
          (base + stride) + (2 * stride) * posToNat p =
            base + stride * (2 * posToNat p + 1) := by
        rw [Nat.mul_comm 2 stride, Nat.mul_assoc stride 2 (posToNat p),
          Nat.add_assoc base stride (stride * (2 * posToNat p))]
        have hs :
            stride + stride * (2 * posToNat p) =
              stride * (2 * posToNat p + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        rw [hs]
      rw [harith]

/-- Out-of-bounds lookup law for `RawTree.tabulateGo` (`depth < posDepth k`). -/
theorem rawTree_get_tabulateGo_oob {α : Type} :
    ∀ (depth base stride : Nat) (f : Nat → Option α) (k : Pos),
      depth < posDepth k →
      RawTree.get (RawTree.tabulateGo depth base stride f) k = none
  | 0, _, _, _, _, _ => rfl
  | d + 1, base, stride, f, k, hk => by
    change RawTree.get
        (RawTree.make
          (RawTree.tabulateGo d base (2 * stride) f)
          (f (base + stride - 1))
          (RawTree.tabulateGo d (base + stride) (2 * stride) f)) k = none
    rw [rawTree_get_make]
    cases k with
    | xH =>
      exact False.elim (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le d)) hk)
    | xO p =>
      exact rawTree_get_tabulateGo_oob d base (2 * stride) f p
        (Nat.lt_of_succ_lt_succ hk)
    | xI p =>
      exact rawTree_get_tabulateGo_oob d (base + stride) (2 * stride) f p
        (Nat.lt_of_succ_lt_succ hk)

/-- In-bounds `Pos` lookup equivalence for `ptreeTabulate`. -/
theorem ptree_get_tabulate_in {α : Type} (depth : Nat) (f : Nat → Option α)
    {k : Pos} (hk : posDepth k ≤ depth) :
    (ptreeTabulate depth f).get k = f (posToNat k - 1) := by
  unfold ptreeTabulate PTree.get
  dsimp only
  rw [rawTree_get_tabulateGo_in depth 0 1 f k hk, Nat.one_mul, Nat.zero_add]

/-- Out-of-bounds `Pos` lookup law for `ptreeTabulate`. -/
theorem ptree_get_tabulate_oob {α : Type} (depth : Nat) (f : Nat → Option α)
    {k : Pos} (hk : depth < posDepth k) :
    (ptreeTabulate depth f).get k = none :=
  rawTree_get_tabulateGo_oob depth 0 1 f k hk

/-- In-bounds `Nat` lookup equivalence for `ptreeTabulate`: for all `n` with
`n + 1 < ptreePow2 depth`, `(ptreeTabulate depth f).get (natToPos n) = f n`.
-/
theorem ptree_get_tabulate_nat_in {α : Type} (depth : Nat) (f : Nat → Option α)
    {n : Nat} (hn : n + 1 < ptreePow2 depth) :
    (ptreeTabulate depth f).get (natToPos n) = f n := by
  have hDepth : posDepth (natToPos n) ≤ depth :=
    (posDepth_le_iff_lt_pow2 (natToPos n) depth).mpr (by
      rw [posToNat_natToPos n]
      exact hn)
  rw [ptree_get_tabulate_in depth f hDepth, posToNat_natToPos n]
  rfl

/-- Out-of-bounds `Nat` lookup law for `ptreeTabulate`
(`ptreePow2 depth ≤ n + 1`). -/
theorem ptree_get_tabulate_nat_oob {α : Type} (depth : Nat)
    (f : Nat → Option α) {n : Nat} (hn : ptreePow2 depth ≤ n + 1) :
    (ptreeTabulate depth f).get (natToPos n) = none := by
  have hGt : depth < posDepth (natToPos n) := by
    cases Nat.lt_or_ge depth (posDepth (natToPos n)) with
    | inl hlt => exact hlt
    | inr hle =>
      have hLt := (posDepth_le_iff_lt_pow2 (natToPos n) depth).mp hle
      rw [posToNat_natToPos n] at hLt
      exact False.elim (Nat.not_lt_of_ge hn hLt)
  exact ptree_get_tabulate_oob depth f hGt

/-- Logarithmic `O(depth)` conversion of a positive `Nat` `m ≥ 1` into `Pos`
via `@Nat.rec` (`0` `noncomputable`), avoiding unary `natToPos` stack depth on
large indices (`natToPosFast 255` takes 9 steps instead of 255). -/
def posOfNatFuel (fuel : Nat) : Nat → Pos :=
  @Nat.rec (fun _ => Nat → Pos)
    (fun _ => .xH)
    (fun _ ih m =>
      cond (Nat.ble m 1) .xH
        (cond (Nat.beq (Nat.mod m 2) 0)
          (.xO (ih (Nat.div m 2)))
          (.xI (ih (Nat.div m 2)))))
    fuel

/-- Logarithmic `O(depth)` encoder mapping `n : Nat` to `Pos` representing
`n + 1` (exact for all `n + 1 < ptreePow2 depth`). -/
def natToPosAt (depth n : Nat) : Pos :=
  posOfNatFuel depth (n + 1)

private theorem posToNat_inj : ∀ {a b : Pos}, posToNat a = posToNat b → a = b
  | .xH, .xH, _ => rfl
  | .xH, .xO p, h => by
    have h2 : 2 ≤ 2 * posToNat p := Nat.mul_le_mul_left 2 (posToNat_pos p)
    change 1 = 2 * posToNat p at h
    rw [← h] at h2
    exact False.elim (Nat.not_lt_of_ge h2 (Nat.lt_succ_self 1))
  | .xH, .xI p, h => by
    have h2 : 2 ≤ 2 * posToNat p := Nat.mul_le_mul_left 2 (posToNat_pos p)
    have h3 : 3 ≤ 2 * posToNat p + 1 := Nat.succ_le_succ h2
    change 1 = 2 * posToNat p + 1 at h
    rw [← h] at h3
    exact False.elim (Nat.not_lt_of_ge h3 (Nat.lt_succ_of_lt (Nat.lt_succ_self 1)))
  | .xO p, .xH, h => by
    have h2 : 2 ≤ 2 * posToNat p := Nat.mul_le_mul_left 2 (posToNat_pos p)
    change 2 * posToNat p = 1 at h
    rw [h] at h2
    exact False.elim (Nat.not_lt_of_ge h2 (Nat.lt_succ_self 1))
  | .xI p, .xH, h => by
    have h2 : 2 ≤ 2 * posToNat p := Nat.mul_le_mul_left 2 (posToNat_pos p)
    have h3 : 3 ≤ 2 * posToNat p + 1 := Nat.succ_le_succ h2
    change 2 * posToNat p + 1 = 1 at h
    rw [h] at h3
    exact False.elim (Nat.not_lt_of_ge h3 (Nat.lt_succ_of_lt (Nat.lt_succ_self 1)))
  | .xO a, .xO b, h => by
    change 2 * posToNat a = 2 * posToNat b at h
    have he : posToNat a = posToNat b :=
      Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 1) h
    exact congrArg Pos.xO (posToNat_inj he)
  | .xI a, .xI b, h => by
    change 2 * posToNat a + 1 = 2 * posToNat b + 1 at h
    have he : posToNat a = posToNat b :=
      Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 1) (Nat.succ.inj h)
    exact congrArg Pos.xI (posToNat_inj he)
  | .xO a, .xI b, h => by
    change 2 * posToNat a = 2 * posToNat b + 1 at h
    have hm : Nat.mod (2 * posToNat a) 2 = Nat.mod (2 * posToNat b + 1) 2 :=
      congrArg (fun z => Nat.mod z 2) h
    have hL : Nat.mod (2 * posToNat a) 2 = 0 := Nat.mul_mod_right 2 (posToNat a)
    have hR : Nat.mod (2 * posToNat b + 1) 2 = Nat.mod 1 2 :=
      Nat.mul_add_mod_self_left 2 (posToNat b) 1
    rw [hL, hR] at hm
    cases hm
  | .xI a, .xO b, h => by
    change 2 * posToNat a + 1 = 2 * posToNat b at h
    have hm : Nat.mod (2 * posToNat a + 1) 2 = Nat.mod (2 * posToNat b) 2 :=
      congrArg (fun z => Nat.mod z 2) h
    have hL : Nat.mod (2 * posToNat a + 1) 2 = Nat.mod 1 2 :=
      Nat.mul_add_mod_self_left 2 (posToNat a) 1
    have hR : Nat.mod (2 * posToNat b) 2 = 0 := Nat.mul_mod_right 2 (posToNat b)
    rw [hL, hR] at hm
    cases hm

private theorem posToNat_posOfNatFuel :
    ∀ (fuel m : Nat), 0 < m → m < ptreePow2 fuel →
      posToNat (posOfNatFuel fuel m) = m
  | 0, m, hPos, hLt =>
    False.elim (Nat.not_lt_of_ge hPos hLt)
  | d + 1, m, hPos, hLt => by
    change posToNat
      (cond (Nat.ble m 1) .xH
        (cond (Nat.beq (Nat.mod m 2) 0)
          (.xO (posOfNatFuel d (Nat.div m 2)))
          (.xI (posOfNatFuel d (Nat.div m 2))))) = m
    cases h1 : Nat.ble m 1 with
    | true =>
      dsimp only [cond, posToNat]
      exact (Nat.le_antisymm (Nat.le_of_ble_eq_true h1) hPos).symm
    | false =>
      dsimp only [cond]
      have hGe2 : 2 ≤ m := by
        cases Nat.lt_or_ge m 2 with
        | inr hg => exact hg
        | inl hl =>
          have hLe1 : m ≤ 1 := Nat.le_of_lt_succ hl
          have hbt := Nat.ble_eq_true_of_le hLe1
          rw [h1] at hbt
          cases hbt
      have hHalfPos : 0 < Nat.div m 2 := by
        have h1le : 1 ≤ Nat.div m 2 :=
          (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hGe2
        exact h1le
      have hHalfLt : Nat.div m 2 < ptreePow2 d := by
        change m < 2 * ptreePow2 d at hLt
        rw [Nat.mul_comm 2 (ptreePow2 d)] at hLt
        exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hLt
      have hdm : 2 * Nat.div m 2 + Nat.mod m 2 = m := Nat.div_add_mod m 2
      have hModLt : Nat.mod m 2 < 2 := Nat.mod_lt m (Nat.succ_pos 1)
      cases hp : Nat.beq (Nat.mod m 2) 0 with
      | true =>
        dsimp only [cond, posToNat]
        rw [posToNat_posOfNatFuel d (Nat.div m 2) hHalfPos hHalfLt]
        have hz := Nat.eq_of_beq_eq_true hp
        rw [hz, Nat.add_zero] at hdm
        exact hdm
      | false =>
        dsimp only [cond, posToNat]
        rw [posToNat_posOfNatFuel d (Nat.div m 2) hHalfPos hHalfLt]
        cases hmv : Nat.mod m 2 with
        | zero => rw [hmv] at hp; cases hp
        | succ r =>
          cases r with
          | zero =>
            rw [hmv] at hdm
            exact hdm
          | succ r' =>
            rw [hmv] at hModLt
            exact False.elim
              (Nat.not_lt_of_ge (Nat.le_add_left 2 r') hModLt)

/-- Logarithmic `natToPosAt depth n` agrees identically with `natToPos n`
whenever `n + 1 < ptreePow2 depth`. -/
theorem natToPosAt_eq_natToPos {depth n : Nat} (h : n + 1 < ptreePow2 depth) :
    natToPosAt depth n = natToPos n :=
  posToNat_inj (by
    rw [posToNat_natToPos n]
    exact posToNat_posOfNatFuel depth (n + 1) (Nat.succ_pos n) h)

/-! ## 5. Kernel-Checked Canaries -/

/-- Canary: disjoint-key `PTree.set` updates commute by `rfl` without axioms.
-/
theorem canary_disjoint_set_comm :
    (PTree.empty.set (natToPos 2) 10).set (natToPos 5) 20 =
      (PTree.empty.set (natToPos 5) 20).set (natToPos 2) 10 := rfl

/-- Canary: deleting every inserted key re-canonicalizes back to `PTree.empty`.
-/
theorem canary_remove_to_empty :
    (((PTree.empty.set (natToPos 2) 10).set (natToPos 5) 20).remove
      (natToPos 2)).remove (natToPos 5) = PTree.empty := rfl

private noncomputable def canaryGoalTree : PTree Nat :=
  ((PTree.empty.set (natToPos 1) 10).set (natToPos 2) 20).set (natToPos 3) 30

private noncomputable def canaryReqTree : PTree Nat :=
  (PTree.empty.set (natToPos 1) 10).set (natToPos 3) 30

private noncomputable def canaryRemTree : PTree Nat :=
  PTree.empty.set (natToPos 2) 20

private theorem canary_diffWith_eval :
    PTree.diffWith Nat.beq canaryGoalTree canaryReqTree = some canaryRemTree :=
  rfl

/-- Canary: `PTree.diffWith Nat.beq` splits `canaryGoalTree` into disjoint
`canaryReqTree` and `canaryRemTree` whose union equals `canaryGoalTree`. -/
theorem canary_diffWith_frame :
    PTree.DisjointProp canaryReqTree canaryRemTree ∧
      PTree.union canaryReqTree canaryRemTree = canaryGoalTree :=
  ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true canary_diffWith_eval

/-- Canary: disjoint `PTree.union` commutes on framed sub-tries. -/
theorem canary_union_disjoint_comm :
    PTree.union canaryReqTree canaryRemTree =
      PTree.union canaryRemTree canaryReqTree :=
  ptree_union_comm_of_disjoint canary_diffWith_frame.1

/-- Canary: `PTree.diffWith` on empty maps returns `some PTree.empty`. -/
theorem canary_empty_diffWith_empty :
    PTree.diffWith Nat.beq (PTree.empty : PTree Nat) PTree.empty =
      some PTree.empty := rfl

/-- Canary: `PTree.diffWith` subtracting `canaryGoalTree` from itself
re-canonicalizes cleanly to `some PTree.empty`. -/
theorem canary_diffWith_self :
    PTree.diffWith Nat.beq canaryGoalTree canaryGoalTree =
      some PTree.empty := rfl

/-- Negative canary: `PTree.diffWith Nat.beq` fails closed (`none`) when a
required key is absent from `PTree.empty`. -/
theorem canary_diffWith_missing_on_empty :
    PTree.diffWith Nat.beq PTree.empty (PTree.empty.set (natToPos 4) 1) =
      none := rfl

/-- Negative canary: `PTree.diffWith Nat.beq` fails closed (`none`) when a
required key has a mismatched value. -/
theorem canary_diffWith_mismatch :
    PTree.diffWith Nat.beq canaryGoalTree (PTree.empty.set (natToPos 1) 99) =
      none := rfl

/-- 256-entry top-down `ptreeTabulate` scaling canary (`depth = 9`, covering
indices `0..510`): surgical lookups via logarithmic `natToPosAt` at `0`, `127`,
`255`, and out-of-bounds `256` / `511` reduce by `rfl` forcing only `O(log N)`
spine nodes. -/
theorem canary_ptreeTabulate_256 :
    let t := ptreeTabulate 9
      (fun i => cond (Nat.blt i 256) (some (i * 3 + 1)) none)
    t.get (natToPosAt 9 0) = some 1 ∧
    t.get (natToPosAt 9 127) = some 382 ∧
    t.get (natToPosAt 9 255) = some 766 ∧
    t.get (natToPosAt 9 256) = none ∧
    t.get (natToPosAt 10 511) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PTree
