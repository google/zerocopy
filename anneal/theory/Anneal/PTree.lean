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

/-!
# Canonical Positive Binary Radix Trie (`Anneal.PTree`)

Pass-1-portable (`prelude` + locked `Init.*` only, zero `._unsafe_rec`, allowed
theory tactics only) Appel-Leroy canonical positive radix trie `PTree α`:

- Every finite map has a unique canonical representation
  (`RawTree.isCanon = true`), giving axiom-free extensional equality
  `ptree_eq_of_get` (zero Lean axioms: no `funext`, no `Classical.choice`, no
  `Quot.sound`) so disjoint updates commute definitionally (`rfl`) on concrete
  keys.
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

/-! ## 4. Kernel-Checked Canaries -/

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

end Anneal.PTree
