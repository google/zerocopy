-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Cluster A2: State Map Representations & Join-Point Normalization

Self-contained `prelude` + `Init.NotationExtra` formalization comparing five
state map representations for kernel-checked symbolic execution in Lean 4.34.1:

1. **Rep 1 (`FnMap`)**: Function closure `Nat → Option V` (`updateSlot`).
2. **Rep 2 (`DenseList` & `CanonList`)**: Positional `List (Option V)` (fixed
   length via `List.set`, plus auto-padding/auto-trimming `CanonList`).
3. **Rep 3 (`DenseArray`)**: Lean `Array (Option V)` (`Array.setIfInBounds` and
   `getElem?`).
4. **Rep 4 (`SortedAList`)**: Canonical key-sorted association list
   `List (Nat × V)` with `none` erasure.
5. **Rep 5 (`BinTrie`)**: Canonical binary radix trie indexed by bijective
   bit-paths `List Bool`, with smart constructor `mkNode` collapsing empty
   subtrees (`.node none .leaf .leaf ↦ .leaf`).
-/

namespace StateMapBenchmarks

/-- Abstract symbolic value domain representing `X86Val` in kernel symbolic
execution. -/
inductive Val where
  | word64 (n : Nat)
  | pair (a b : Val)
  deriving DecidableEq

/-- Helper lemma: `(i + 1 == j + 1) = (i == j)` in `prelude` +
`Init.NotationExtra`. -/
theorem nat_beq_succ (i j : Nat) : ((i + 1) == (j + 1)) = (i == j) := by
  cases h : i == j with
  | true =>
    have hij : i = j := of_decide_eq_true h
    subst hij
    exact decide_eq_true rfl
  | false =>
    have hne : i ≠ j := of_decide_eq_false h
    exact decide_eq_false (fun hc => by injection hc with h'; exact hne h')

/-!
## Representation 1: `FnMap` (`Nat → Option V`)

Matches `Trusted/X86Semantics.lean` (`mem : Nat → Option X86Val` and
`updateSlot`).
-/

abbrev FnMap (V : Type) := Nat → Option V

def FnMap.empty {V : Type} : FnMap V := fun _ => none

def FnMap.get {V : Type} (m : FnMap V) (idx : Nat) : Option V := m idx

def FnMap.set {V : Type} (m : FnMap V) (idx : Nat) (val : Option V) : FnMap V :=
  fun i => if i == idx then val else m i

theorem FnMap.get_set {V : Type} (m : FnMap V) (target : Nat) (val : Option V)
    (i : Nat) :
    FnMap.get (FnMap.set m target val) i =
      if i == target then val else FnMap.get m i :=
  rfl

/-!
## Representation 2a: `DenseList` (Fixed-Length `List (Option V)`)

Positional list initialized to `List.replicate numSlots none`, accessed via
`List.getElem?` (`m[idx]?`) and updated via `List.set`.
-/

abbrev DenseList (V : Type) := List (Option V)

def DenseList.init {V : Type} : Nat → DenseList V
  | 0 => []
  | n + 1 => none :: DenseList.init n

def DenseList.get {V : Type} : DenseList V → Nat → Option V
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, i + 1 => DenseList.get xs i

def DenseList.set {V : Type} : DenseList V → Nat → Option V → DenseList V
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: DenseList.set xs i v

/-!
## Representation 2b: `CanonList` (Auto-Padding & Auto-Trimming `List (Option V)`)

Eliminates the `target < m.length` precondition of `DenseList` by extending the
list with `none` on out-of-bounds writes and collapsing trailing `none`s via
`CanonList.cons`, so `[]` is the unique representation of the empty map and
every finite map has a unique canonical list representation.
-/

abbrev CanonList (V : Type) := List (Option V)

def CanonList.empty {V : Type} : CanonList V := []

def CanonList.cons {V : Type} (x : Option V) (xs : CanonList V) : CanonList V :=
  match x, xs with
  | none, [] => []
  | _, _ => x :: xs

def CanonList.get {V : Type} : CanonList V → Nat → Option V
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, i + 1 => CanonList.get xs i

def CanonList.set {V : Type} : CanonList V → Nat → Option V → CanonList V
  | [], 0, v => CanonList.cons v []
  | [], i + 1, v => CanonList.cons none (CanonList.set [] i v)
  | _ :: xs, 0, v => CanonList.cons v xs
  | x :: xs, i + 1, v => CanonList.cons x (CanonList.set xs i v)

theorem CanonList.get_cons {V : Type} (x : Option V) (xs : CanonList V)
    (i : Nat) :
    CanonList.get (CanonList.cons x xs) i = CanonList.get (x :: xs) i := by
  cases x with
  | some _ => rfl
  | none =>
    cases xs with
    | nil => cases i <;> rfl
    | cons _ _ => rfl

theorem CanonList.get_set_nil {V : Type} (target : Nat) (val : Option V)
    (i : Nat) :
    CanonList.get (CanonList.set [] target val) i =
      if i == target then val else none := by
  induction target generalizing i with
  | zero =>
    dsimp [CanonList.set]
    rw [CanonList.get_cons]
    cases i <;> rfl
  | succ t ih =>
    dsimp [CanonList.set]
    rw [CanonList.get_cons]
    cases i with
    | zero => rfl
    | succ i' =>
      dsimp [CanonList.get]
      rw [nat_beq_succ]
      exact ih i'

theorem CanonList.get_set {V : Type} (m : CanonList V) (target : Nat)
    (val : Option V) (i : Nat) :
    CanonList.get (CanonList.set m target val) i =
      if i == target then val else CanonList.get m i := by
  induction m generalizing target i with
  | nil => exact CanonList.get_set_nil target val i
  | cons x xs ih =>
    cases target with
    | zero =>
      dsimp [CanonList.set]
      rw [CanonList.get_cons]
      cases i <;> rfl
    | succ t =>
      dsimp [CanonList.set]
      rw [CanonList.get_cons]
      cases i with
      | zero => rfl
      | succ i' =>
        dsimp [CanonList.get]
        rw [nat_beq_succ]
        exact ih t i'

/-!
## Representation 3: `DenseArray` (`Array (Option V)`)

Uses Lean's `Array (Option V)`. Note that inside the Lean 4 kernel typechecker,
`Array` is a wrapper structure around `toList : List (Option V)` without special
kernel array reduction rules, so `Array.setIfInBounds` and `getElem?` unfold to
list operations plus decidable bounds checks.
-/

abbrev DenseArray (V : Type) := Array (Option V)

def DenseArray.init {V : Type} (n : Nat) : DenseArray V :=
  (DenseList.init n).toArray

def DenseArray.get {V : Type} (m : DenseArray V) (idx : Nat) : Option V :=
  match m[idx]? with
  | some v => v
  | none => none

def DenseArray.set {V : Type} (m : DenseArray V) (idx : Nat) (val : Option V) :
    DenseArray V :=
  m.setIfInBounds idx val

/-!
## Representation 4: `SortedAList` (Canonical Sorted Association List)

Stores only live slots `(k, v)` in strictly increasing key order `k₀ < k₁ < ...`.
Writing `none` removes the key completely, ensuring unique canonical
representation.
-/

abbrev SortedAList (V : Type) := List (Nat × V)

def SortedAList.empty {V : Type} : SortedAList V := []

def SortedAList.get {V : Type} : SortedAList V → Nat → Option V
  | [], _ => none
  | (k, v) :: rest, idx =>
    if idx == k then some v
    else if idx < k then none
    else SortedAList.get rest idx

def SortedAList.insert {V : Type} : SortedAList V → Nat → V → SortedAList V
  | [], idx, val => [(idx, val)]
  | (k, v) :: rest, idx, val =>
    if idx == k then (idx, val) :: rest
    else if idx < k then (idx, val) :: (k, v) :: rest
    else (k, v) :: SortedAList.insert rest idx val

def SortedAList.erase {V : Type} : SortedAList V → Nat → SortedAList V
  | [], _ => []
  | (k, v) :: rest, idx =>
    if idx == k then rest
    else if idx < k then (k, v) :: rest
    else (k, v) :: SortedAList.erase rest idx

def SortedAList.set {V : Type} (m : SortedAList V) (idx : Nat) :
    Option V → SortedAList V
  | some val => SortedAList.insert m idx val
  | none => SortedAList.erase m idx

/-!
## Representation 5: `BinTrie` (Canonical Binary Radix Trie)

Uses a bijective bit-path encoding `natToBits : Nat → List Bool` (`0 ↦ []`,
`1 ↦ [false]`, `2 ↦ [true]`, `3 ↦ [false, false]`, ...) so that `getBits` and
`setBits` are 100% structurally recursive on `List Bool`. The smart constructor
`BinTrie.mkNode` collapses `.node none .leaf .leaf` to `.leaf`, guaranteeing
that every finite map has a unique canonical tree spine.
-/

inductive BinTrie (V : Type) where
  | leaf
  | node (val : Option V) (left right : BinTrie V)

/-- Strict smart constructor: pattern-matches on `l` and `r` first so that WHNF
evaluation of `BinTrie.setBits` forces the entire modified root-to-leaf spine,
and collapses empty subtrees `.node none .leaf .leaf` into `.leaf`. -/
def BinTrie.mkNode {V : Type} (v : Option V) (l r : BinTrie V) : BinTrie V :=
  match l, r with
  | .leaf, .leaf =>
    match v with
    | none => .leaf
    | some _ => .node v .leaf .leaf
  | .leaf, .node _ _ _ => .node v l r
  | .node _ _ _, .leaf => .node v l r
  | .node _ _ _, .node _ _ _ => .node v l r

def BinTrie.getBits {V : Type} : BinTrie V → List Bool → Option V
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l _, false :: bs => BinTrie.getBits l bs
  | .node _ _ r, true :: bs => BinTrie.getBits r bs

def BinTrie.setBits {V : Type} : BinTrie V → List Bool → Option V → BinTrie V
  | .leaf, [], val => BinTrie.mkNode val .leaf .leaf
  | .leaf, false :: bs, val =>
    BinTrie.mkNode none (BinTrie.setBits .leaf bs val) .leaf
  | .leaf, true :: bs, val =>
    BinTrie.mkNode none .leaf (BinTrie.setBits .leaf bs val)
  | .node _ l r, [], val => BinTrie.mkNode val l r
  | .node v l r, false :: bs, val =>
    BinTrie.mkNode v (BinTrie.setBits l bs val) r
  | .node v l r, true :: bs, val =>
    BinTrie.mkNode v l (BinTrie.setBits r bs val)

theorem BinTrie.getBits_mkNode {V : Type} (v : Option V) (l r : BinTrie V)
    (bs : List Bool) :
    BinTrie.getBits (BinTrie.mkNode v l r) bs =
      BinTrie.getBits (.node v l r) bs := by
  cases l with
  | node _ _ _ => cases r <;> rfl
  | leaf =>
    cases r with
    | node _ _ _ => rfl
    | leaf =>
      cases v with
      | some _ => rfl
      | none =>
        cases bs with
        | nil => rfl
        | cons b _ => cases b <;> rfl

theorem BinTrie.getBits_setBits {V : Type} (t : BinTrie V) (target : List Bool)
    (val : Option V) (bs : List Bool) :
    BinTrie.getBits (BinTrie.setBits t target val) bs =
      if bs == target then val else BinTrie.getBits t bs := by
  induction target generalizing t bs with
  | nil =>
    cases t <;> {
      dsimp [BinTrie.setBits]
      rw [BinTrie.getBits_mkNode]
      cases bs with
      | nil => rfl
      | cons b _ => cases b <;> rfl
    }
  | cons tb tbs ih =>
    cases tb with
    | false =>
      cases t with
      | leaf =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | true => rfl
          | false =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih .leaf bs'
      | node v l r =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | true => rfl
          | false =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih l bs'
    | true =>
      cases t with
      | leaf =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | false => rfl
          | true =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih .leaf bs'
      | node v l r =>
        dsimp [BinTrie.setBits]
        rw [BinTrie.getBits_mkNode]
        cases bs with
        | nil => rfl
        | cons b bs' =>
          cases b with
          | false => rfl
          | true =>
            dsimp [BinTrie.getBits, BEq.beq, List.beq]
            exact ih r bs'

def succBits : List Bool → List Bool
  | [] => [false]
  | false :: bs => true :: bs
  | true :: bs => false :: succBits bs

def natToBits : Nat → List Bool
  | 0 => []
  | n + 1 => succBits (natToBits n)

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

def bitsToNat : List Bool → Nat
  | [] => 0
  | false :: bs => double (bitsToNat bs) + 1
  | true :: bs => double (bitsToNat bs) + 2

theorem bitsToNat_succBits (bs : List Bool) :
    bitsToNat (succBits bs) = bitsToNat bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => rfl
    | true =>
      dsimp [succBits, bitsToNat]
      rw [ih]
      rfl

theorem bitsToNat_natToBits (n : Nat) :
    bitsToNat (natToBits n) = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [natToBits]
    rw [bitsToNat_succBits, ih]

theorem natToBits_injective {i j : Nat} (h : natToBits i = natToBits j) :
    i = j := by
  rw [← bitsToNat_natToBits i, ← bitsToNat_natToBits j, h]

theorem list_bool_beq_eq {bs1 bs2 : List Bool} :
    (bs1 == bs2) = decide (bs1 = bs2) := by
  induction bs1 generalizing bs2 with
  | nil =>
    cases bs2 <;> rfl
  | cons b1 r1 ih =>
    cases bs2 with
    | nil => rfl
    | cons b2 r2 =>
      cases b1 <;> cases b2
      · change (r1 == r2) = decide (false :: r1 = false :: r2)
        rw [ih]
        cases h : decide (r1 = r2) with
        | true =>
          have hr : r1 = r2 := of_decide_eq_true h
          subst hr
          exact (decide_eq_true rfl).symm
        | false =>
          have hne : r1 ≠ r2 := of_decide_eq_false h
          exact (decide_eq_false
            (fun hc => by injection hc with _ h'; exact hne h')).symm
      · rfl
      · rfl
      · change (r1 == r2) = decide (true :: r1 = true :: r2)
        rw [ih]
        cases h : decide (r1 = r2) with
        | true =>
          have hr : r1 = r2 := of_decide_eq_true h
          subst hr
          exact (decide_eq_true rfl).symm
        | false =>
          have hne : r1 ≠ r2 := of_decide_eq_false h
          exact (decide_eq_false
            (fun hc => by injection hc with _ h'; exact hne h')).symm

theorem natToBits_beq (i j : Nat) :
    (natToBits i == natToBits j) = (i == j) := by
  rw [list_bool_beq_eq]
  cases h : i == j with
  | true =>
    have hij : i = j := of_decide_eq_true h
    subst hij
    exact decide_eq_true rfl
  | false =>
    have hne : i ≠ j := of_decide_eq_false h
    exact decide_eq_false (fun hbits => hne (natToBits_injective hbits))

def BinTrie.empty {V : Type} : BinTrie V := .leaf

def BinTrie.get {V : Type} (t : BinTrie V) (idx : Nat) : Option V :=
  BinTrie.getBits t (natToBits idx)

def BinTrie.set {V : Type} (t : BinTrie V) (idx : Nat) (val : Option V) :
    BinTrie V :=
  BinTrie.setBits t (natToBits idx) val

theorem BinTrie.get_set {V : Type} (t : BinTrie V) (target : Nat)
    (val : Option V) (i : Nat) :
    BinTrie.get (BinTrie.set t target val) i =
      if i == target then val else BinTrie.get t i := by
  dsimp [BinTrie.get, BinTrie.set]
  rw [BinTrie.getBits_setBits, natToBits_beq]

/-!
## Deliverable 2: Canonicity & Join-Point Definitional Equality (`rfl`)

We test all representations on symbolic values `v1 v2 v3 v4 retVal tmp : Val`:

1. **Test A (Disjoint Update Commutativity by `rfl`)**:
   `set (set m0 1 (some v1)) 3 (some v2) = set (set m0 3 (some v2)) 1 (some v1)`
2. **Test B (Dead-Slot Erasure by `rfl`)**:
   `set (set m 4 (some tmp)) 4 none = m`
3. **Test C (Asymmetric CFG Join-Point Equivalence by `rfl`)**:
   - Branch 1 writes temporary slot 4 (`some tmp`), writes return slot 0
     (`some retVal`), then erases temporary slot 4 (`none`).
   - Branch 2 writes temporary slot 3 (`some v3`), writes return slot 0
     (`some retVal`), then erases temporary slot 3 (`none`).
   - Both branches are definitionally equal (`rfl`) at the join point!
-/

section CanonicityTests
variable (v1 v2 v3 v4 retVal tmp : Val)

-- Test A: Disjoint Update Commutativity by `rfl`
theorem denseList_comm_rfl :
    DenseList.set (DenseList.set (DenseList.init 6) 1 (some v1)) 3 (some v2) =
    DenseList.set (DenseList.set (DenseList.init 6) 3 (some v2)) 1 (some v1) :=
  rfl

theorem canonList_comm_rfl :
    CanonList.set (CanonList.set CanonList.empty 1 (some v1)) 3 (some v2) =
    CanonList.set (CanonList.set CanonList.empty 3 (some v2)) 1 (some v1) :=
  rfl

theorem denseArray_comm_rfl :
    DenseArray.set (DenseArray.set (DenseArray.init 6) 1 (some v1)) 3 (some v2) =
    DenseArray.set (DenseArray.set (DenseArray.init 6) 3 (some v2)) 1 (some v1) :=
  rfl

theorem sortedAList_comm_rfl :
    SortedAList.set (SortedAList.set SortedAList.empty 1 (some v1)) 3 (some v2) =
    SortedAList.set (SortedAList.set SortedAList.empty 3 (some v2)) 1 (some v1) :=
  rfl

theorem binTrie_comm_rfl :
    BinTrie.set (BinTrie.set BinTrie.empty 1 (some v1)) 3 (some v2) =
    BinTrie.set (BinTrie.set BinTrie.empty 3 (some v2)) 1 (some v1) :=
  rfl

-- Test B: Dead-Slot Erasure by `rfl`
theorem denseList_erase_rfl :
    let m0 := DenseList.set (DenseList.init 6) 1 (some v1)
    DenseList.set (DenseList.set m0 4 (some tmp)) 4 none = m0 :=
  rfl

theorem canonList_erase_rfl :
    let m0 := CanonList.set CanonList.empty 1 (some v1)
    CanonList.set (CanonList.set m0 4 (some tmp)) 4 none = m0 :=
  rfl

theorem denseArray_erase_rfl :
    let m0 := DenseArray.set (DenseArray.init 6) 1 (some v1)
    DenseArray.set (DenseArray.set m0 4 (some tmp)) 4 none = m0 :=
  rfl

theorem sortedAList_erase_rfl :
    let m0 := SortedAList.set SortedAList.empty 1 (some v1)
    SortedAList.set (SortedAList.set m0 4 (some tmp)) 4 none = m0 :=
  rfl

theorem binTrie_erase_rfl :
    let m0 := BinTrie.set BinTrie.empty 1 (some v1)
    BinTrie.set (BinTrie.set m0 4 (some tmp)) 4 none = m0 :=
  rfl

-- Test C: Asymmetric CFG Join-Point Equivalence by `rfl`
theorem denseList_asymmetric_join_rfl :
    let mInit :=
      DenseList.set (DenseList.set (DenseList.init 6) 1 (some v1)) 2 (some v2)
    let branch1 :=
      DenseList.set
        (DenseList.set (DenseList.set mInit 4 (some tmp)) 0 (some retVal))
        4 none
    let branch2 :=
      DenseList.set
        (DenseList.set (DenseList.set mInit 3 (some v3)) 0 (some retVal))
        3 none
    branch1 = branch2 :=
  rfl

theorem canonList_asymmetric_join_rfl :
    let mInit :=
      CanonList.set (CanonList.set CanonList.empty 1 (some v1)) 2 (some v2)
    let branch1 :=
      CanonList.set
        (CanonList.set (CanonList.set mInit 4 (some tmp)) 0 (some retVal))
        4 none
    let branch2 :=
      CanonList.set
        (CanonList.set (CanonList.set mInit 3 (some v3)) 0 (some retVal))
        3 none
    branch1 = branch2 :=
  rfl

theorem denseArray_asymmetric_join_rfl :
    let mInit :=
      DenseArray.set
        (DenseArray.set (DenseArray.init 6) 1 (some v1)) 2 (some v2)
    let branch1 :=
      DenseArray.set
        (DenseArray.set (DenseArray.set mInit 4 (some tmp)) 0 (some retVal))
        4 none
    let branch2 :=
      DenseArray.set
        (DenseArray.set (DenseArray.set mInit 3 (some v3)) 0 (some retVal))
        3 none
    branch1 = branch2 :=
  rfl

theorem sortedAList_asymmetric_join_rfl :
    let mInit :=
      SortedAList.set
        (SortedAList.set SortedAList.empty 1 (some v1)) 2 (some v2)
    let branch1 :=
      SortedAList.set
        (SortedAList.set (SortedAList.set mInit 4 (some tmp)) 0 (some retVal))
        4 none
    let branch2 :=
      SortedAList.set
        (SortedAList.set (SortedAList.set mInit 3 (some v3)) 0 (some retVal))
        3 none
    branch1 = branch2 :=
  rfl

theorem binTrie_asymmetric_join_rfl :
    let mInit :=
      BinTrie.set (BinTrie.set BinTrie.empty 1 (some v1)) 2 (some v2)
    let branch1 :=
      BinTrie.set
        (BinTrie.set (BinTrie.set mInit 4 (some tmp)) 0 (some retVal))
        4 none
    let branch2 :=
      BinTrie.set
        (BinTrie.set (BinTrie.set mInit 3 (some v3)) 0 (some retVal))
        3 none
    branch1 = branch2 :=
  rfl

/-!
## Spine Concreteness & Symbolic Arguments

If the initial map is a free variable `m : CanonList Val`, `CanonList.set m 3 v`
cannot unfold because `m`'s constructor (`.nil` vs `.cons`) is unknown.
However, when the initial frame is constructed from a concrete spine containing
symbolic values (`initArgs [v1, v2]`), the spine is 100% concrete while the
payload values `v1, v2 : Val` remain universally quantified free variables. All
subsequent reads, writes, and join-point normalizations then reduce by `rfl`.
-/

def BinTrie.initArgs {V : Type} (args : List V) : BinTrie V :=
  let rec loop : Nat → List V → BinTrie V → BinTrie V
    | _, [], acc => acc
    | idx, a :: rest, acc => loop (idx + 1) rest (BinTrie.set acc idx (some a))
  loop 1 args BinTrie.empty

def CanonList.initArgs {V : Type} (args : List V) : CanonList V :=
  let rec loop : Nat → List V → CanonList V → CanonList V
    | _, [], acc => acc
    | idx, a :: rest, acc => loop (idx + 1) rest (CanonList.set acc idx (some a))
  loop 1 args CanonList.empty

theorem binTrie_symbolic_args_lookup_rfl :
    let m0 := BinTrie.initArgs [v1, v2]
    let m1 := BinTrie.set m0 3 (some v3)
    let m2 := BinTrie.set m1 4 (some v4)
    (BinTrie.get m2 1, BinTrie.get m2 2, BinTrie.get m2 3, BinTrie.get m2 0) =
      (some v1, some v2, some v3, none) :=
  rfl

theorem canonList_symbolic_args_lookup_rfl :
    let m0 := CanonList.initArgs [v1, v2]
    let m1 := CanonList.set m0 3 (some v3)
    let m2 := CanonList.set m1 4 (some v4)
    (CanonList.get m2 1, CanonList.get m2 2, CanonList.get m2 3,
     CanonList.get m2 0) =
      (some v1, some v2, some v3, none) :=
  rfl

end CanonicityTests

end StateMapBenchmarks
