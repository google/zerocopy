-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.ByteArray.Bootstrap
public import Init.Data.String.Bootstrap
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp

public section

/-!
# Balanced `BinChunkTree` Body Resolution and Compositional Shard Bridge

Pass-1-portable (`prelude` + locked `Init.*` + `Trusted.*` + `Anneal.MirWp`
only, zero `sorry`, zero `._unsafe_rec`, axioms `⊆ [propext]`) crate-scale
lookup and verification substrate for Tarjan SCC `.olean` sharding:

1. **`BinChunkTree α`:** Balanced binary span tree caching left-subtree sizes
   (`branch half left right`) so random-access body resolution
   `BinChunkTree.get? tree defId` executes in `⌈log₂ N⌉` GMP comparisons
   (`Nat.blt` / `Nat.sub`) without unfolding sibling SCC shards or hitting
   `defaultMaxRecDepth = 512`.
2. **Exact Equivalence with `Trusted.MirSemantics.getElem?`:**
   `getElem?_toList_eq_get?` bridges `Trusted.MirSemantics.getElem?
   (BinChunkTree.toList tree) defId` directly to `BinChunkTree.get? tree defId`,
   eliminating linear `O(N)` list scans in `BodyVerified` and `ProgramVerified`
   without modifying `trusted/lean/`.
3. **Shard-Local `TreeLocalVerified`:** Decouples per-shard proof obligations
   (`Proof.Shard_k`) from `Captured.program` and sibling shards so editing a
   single function invalidates strictly `O(1)` shard `.olean`s.
4. **`O(N log N)` `ByteDecisionTree` Identity Uniqueness and `O(L)` UTF-8
   Bypass:** Replaces `O(N²)` depth-`N` `bodiesHaveUniqueIdentities` unfolding
   with an `O(log N)`-depth discriminating-byte decision tree over
   `String.toByteArray`, and rewrites `(_root_.String.ofList cs).toByteArray`
   via `string_ofList_bytes_eq` to avoid `O(L²)` `List.toByteArray.loop`
   recursion on long Rust trait-implementation paths.
-/

namespace Anneal.SccSharding

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## 1. Balanced Span-Indexed `BinChunkTree` -/

/-- Balanced binary tree over dense `0`-indexed elements, caching the exact
element count `half` of `left` at every `.branch` node for `O(1)`-per-level
GMP binary search. -/
inductive BinChunkTree (α : Type) where
  | empty : BinChunkTree α
  | leaf (val : α) : BinChunkTree α
  | branch (half : Nat) (left right : BinChunkTree α) : BinChunkTree α

namespace BinChunkTree

/-- Total number of leaf elements in `t` (`@BinChunkTree.rec`, zero
`._unsafe_rec`). -/
@[expose] noncomputable def size {α : Type} (t : BinChunkTree α) : Nat :=
  @BinChunkTree.rec α (fun _ => Nat)
    0
    (fun _ => 1)
    (fun _ _ _ sL sR => sL + sR)
    t

/-- Structural span well-formedness: every `.branch half left right` records
`half = left.size` (`@BinChunkTree.rec`, zero `._unsafe_rec`). -/
@[expose] noncomputable def wf {α : Type} (t : BinChunkTree α) : Bool :=
  @BinChunkTree.rec α (fun _ => Bool)
    true
    (fun _ => true)
    (fun half l _ wfL wfR => Nat.beq (size l) half && (wfL && wfR))
    t

/-- `O(log N)` random-access lookup by 0-based index `idx`
(`@BinChunkTree.rec`, zero `._unsafe_rec`). -/
@[expose] noncomputable def get? {α : Type} (t : BinChunkTree α) (idx : Nat) :
    Option α :=
  @BinChunkTree.rec α (fun _ => Nat → Option α)
    (fun _ => none)
    (fun v i => if Nat.beq i 0 then some v else none)
    (fun half _ _ getL getR i =>
      if Nat.blt i half then getL i else getR (i - half))
    t idx

/-- Flatten `t` into a `List α` via `++` (`@BinChunkTree.rec`, zero
`._unsafe_rec`). -/
@[expose] noncomputable def toList {α : Type} (t : BinChunkTree α) : List α :=
  @BinChunkTree.rec α (fun _ => List α)
    []
    (fun v => [v])
    (fun _ _ _ xs ys => xs ++ ys)
    t

/-- Indexed Boolean predicate check across all leaves of `t` starting at `base`
(`@BinChunkTree.rec`, zero `._unsafe_rec`, depth `O(log N)`). -/
@[expose] noncomputable def allIdx {α : Type} (p : Nat → α → Bool)
    (t : BinChunkTree α) (base : Nat) : Bool :=
  @BinChunkTree.rec α (fun _ => Nat → Bool)
    (fun _ => true)
    (fun v b => p b v)
    (fun half _ _ fL fR b => fL b && fR (b + half))
    t base

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

private theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.ble_eq.mp h

private theorem le_of_blt_false {a b : Nat} (h : Nat.blt a b = false) :
    b ≤ a := by
  refine Nat.not_lt.mp (fun hLt => ?_)
  have hb : Nat.blt a b = true := Nat.ble_eq.mpr hLt
  rw [h] at hb
  nomatch hb

/-- `(toList t).length` equals `size t`. -/
theorem toList_length {α : Type} (t : BinChunkTree α) :
    (toList t).length = size t := by
  induction t with
  | empty => rfl
  | leaf _ => rfl
  | branch half l r ihL ihR =>
    change (toList l ++ toList r).length = size l + size r
    rw [List.length_append, ihL, ihR]

/-- `getElem?` on the left prefix of `xs ++ ys`. -/
theorem getElem?_append_left {α : Type} :
    ∀ {xs ys : List α} {idx : Nat},
      idx < xs.length →
      Trusted.MirSemantics.getElem? (xs ++ ys) idx =
        Trusted.MirSemantics.getElem? xs idx
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, ys, _ + 1, h =>
    getElem?_append_left (xs := rest) (ys := ys) (Nat.lt_of_succ_lt_succ h)

/-- `getElem?` on the right suffix of `xs ++ ys`. -/
theorem getElem?_append_right {α : Type} :
    ∀ {xs ys : List α} {idx : Nat},
      xs.length ≤ idx →
      Trusted.MirSemantics.getElem? (xs ++ ys) idx =
        Trusted.MirSemantics.getElem? ys (idx - xs.length)
  | [], ys, idx, _ => by
    change Trusted.MirSemantics.getElem? ys idx =
      Trusted.MirSemantics.getElem? ys (idx - 0)
    rw [Nat.sub_zero]
  | _ :: _, _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: rest, ys, k + 1, h => by
    change Trusted.MirSemantics.getElem? (rest ++ ys) k =
      Trusted.MirSemantics.getElem? ys ((k + 1) - (rest.length + 1))
    rw [Nat.succ_sub_succ]
    exact getElem?_append_right (Nat.le_of_succ_le_succ h)

/-- Exact equivalence between linear `Trusted.MirSemantics.getElem?` on
`toList t` and `O(log N)` `BinChunkTree.get? t`. -/
theorem getElem?_toList_eq_get? {α : Type} :
    ∀ {t : BinChunkTree α},
      wf t = true →
      ∀ idx : Nat,
        Trusted.MirSemantics.getElem? (toList t) idx = get? t idx := by
  intro t
  induction t with
  | empty =>
    intro _ idx
    cases idx <;> rfl
  | leaf _ =>
    intro _ idx
    cases idx with
    | zero => rfl
    | succ k =>
      cases k <;> rfl
  | branch half l r ihL ihR =>
    intro hwf idx
    change (Nat.beq (size l) half && (wf l && wf r)) = true at hwf
    have hHalf : size l = half := Nat.eq_of_beq_eq_true (bool_and_left hwf)
    have hRest := bool_and_right hwf
    have hWfL : wf l = true := bool_and_left hRest
    have hWfR : wf r = true := bool_and_right hRest
    change Trusted.MirSemantics.getElem? (toList l ++ toList r) idx =
      (if Nat.blt idx half then get? l idx else get? r (idx - half))
    cases hBlt : Nat.blt idx half with
    | true =>
      have hLt : idx < (toList l).length := by
        rw [toList_length l, hHalf]
        exact lt_of_blt hBlt
      rw [getElem?_append_left hLt, ihL hWfL idx]
      rfl
    | false =>
      have hGe : (toList l).length ≤ idx := by
        rw [toList_length l, hHalf]
        exact le_of_blt_false hBlt
      rw [getElem?_append_right hGe, toList_length l, hHalf,
        ihR hWfR (idx - half)]
      rfl

/-- Pointwise soundness of `allIdx`: if `allIdx p t base = true` and
`get? t k = some v`, then `p (base + k) v = true`. -/
theorem allIdx_get? {α : Type} {p : Nat → α → Bool} :
    ∀ {t : BinChunkTree α},
      wf t = true →
      ∀ {base k : Nat} {v : α},
        allIdx p t base = true →
        get? t k = some v →
        p (base + k) v = true := by
  intro t
  induction t with
  | empty =>
    intro _ _ _ _ _ hGet
    nomatch hGet
  | leaf val =>
    intro _ base k v hAll hGet
    dsimp only [get?] at hGet
    cases k with
    | zero =>
      injection hGet with hEq
      subst hEq
      rw [Nat.add_zero]
      exact hAll
    | succ _ =>
      nomatch hGet
  | branch half l r ihL ihR =>
    intro hwf base k v hAll hGet
    change (Nat.beq (size l) half && (wf l && wf r)) = true at hwf
    change (allIdx p l base && allIdx p r (base + half)) = true at hAll
    change (if Nat.blt k half then get? l k else get? r (k - half)) = some v
      at hGet
    have hRest := bool_and_right hwf
    have hWfL : wf l = true := bool_and_left hRest
    have hWfR : wf r = true := bool_and_right hRest
    have hAllL : allIdx p l base = true := bool_and_left hAll
    have hAllR : allIdx p r (base + half) = true := bool_and_right hAll
    cases hBlt : Nat.blt k half with
    | true =>
      rw [hBlt] at hGet
      exact ihL hWfL hAllL hGet
    | false =>
      rw [hBlt] at hGet
      have hGe : half ≤ k := le_of_blt_false hBlt
      have hSub := ihR hWfR hAllR hGet
      have hAdd : base + half + (k - half) = base + k := by
        rw [Nat.add_assoc, Nat.add_sub_of_le hGe]
      rw [hAdd] at hSub
      exact hSub

/-- Non-empty `BinChunkTree` flattens to a non-empty `List`. -/
theorem toList_nonEmpty_of_size_pos {α : Type} {t : BinChunkTree α}
    (hpos : Nat.blt 0 (size t) = true) : !(toList t).isEmpty = true := by
  have hLen : 0 < (toList t).length := by
    rw [toList_length]
    exact lt_of_blt hpos
  cases hXs : toList t with
  | nil =>
    rw [hXs] at hLen
    exact False.elim (Nat.not_lt_zero _ hLen)
  | cons _ _ => rfl

/-- Compositional list-flattening step across `.branch` without unfolding
subtree leaves. -/
theorem toList_branch {α : Type} (half : Nat) (l r : BinChunkTree α)
    {xs ys : List α} (hL : xs = toList l) (hR : ys = toList r) :
    List.append xs ys = toList (.branch half l r) := by
  change xs ++ ys = toList l ++ toList r
  rw [hL, hR]

/-- Compositional `size` aggregation across `.branch` without unfolding
subtree leaves. -/
theorem size_branch {α : Type} (half : Nat) (l r : BinChunkTree α)
    {sL sR s : Nat} (hL : size l = sL) (hR : size r = sR)
    (hSum : sL + sR = s) :
    size (.branch half l r) = s := by
  change size l + size r = s
  rw [hL, hR, hSum]

/-- Compositional `wf` aggregation across `.branch` without unfolding
subtree leaves. -/
theorem wf_branch {α : Type} {half : Nat} {l r : BinChunkTree α}
    (hSize : size l = half) (hL : wf l = true) (hR : wf r = true) :
    wf (.branch half l r) = true := by
  change (Nat.beq (size l) half && (wf l && wf r)) = true
  rw [hSize, Nat.beq_refl, hL, hR]
  rfl

/-- Compositional `allIdx` leaf constructor. -/
theorem allIdx_leaf {α : Type} {p : Nat → α → Bool} {base : Nat} {v : α}
    (h : p base v = true) :
    allIdx p (.leaf v) base = true := h

/-- Compositional `allIdx` aggregation across `.branch` without unfolding
subtree leaves or decision-tree predicates. -/
theorem allIdx_branch {α : Type} {p : Nat → α → Bool}
    {half base nextBase : Nat} {l r : BinChunkTree α}
    (hNext : base + half = nextBase)
    (hL : allIdx p l base = true)
    (hR : allIdx p r nextBase = true) :
    allIdx p (.branch half l r) base = true := by
  change (allIdx p l base && allIdx p r (base + half)) = true
  rw [hNext, hL, hR]
  rfl

end BinChunkTree

/-! ## 2. `O(N log N)` Discriminating-Byte Decision Tree for Uniqueness -/

/-- Balanced identity decision tree mapping UTF-8 byte lists of `Body.identity`
values injectively back to their expected `DefId` in `O(log N)` worst-case
depth (`splitByte` on balanced single-byte cuts, `splitTag` checksum fallback,
and `splitLex` lexicographic-midpoint fallback when earlier cuts cannot
balance). -/
inductive ByteDecisionTree where
  | fail : ByteDecisionTree
  | leaf (expectedDefId : Nat) : ByteDecisionTree
  | splitByte (pos : Nat) (threshold : Nat)
      (ltBranch geBranch : ByteDecisionTree) : ByteDecisionTree
  | splitTag (threshold : Nat)
      (ltBranch geBranch : ByteDecisionTree) : ByteDecisionTree
  | splitLex (pivot : List UInt8)
      (leBranch gtBranch : ByteDecisionTree) : ByteDecisionTree

/-- Total byte lookup returning `0..255` in bounds and sentinel `256` at or
past EOF. -/
@[expose] noncomputable def byteCodeAt (bs : List UInt8) (pos : Nat) : Nat :=
  match Trusted.MirSemantics.getElem? bs pos with
  | none => 256
  | some b => b.toNat

/-- Lexicographic `≤` comparison over `List UInt8` (`8` bytes per recursive
call via `Trusted.MirSemantics.byteListCmp8`). -/
@[expose] noncomputable def byteListLe (xs ys : List UInt8) : Bool :=
  match Trusted.MirSemantics.byteListCmp8 xs ys with
  | .gt => false
  | _ => true

/-- Evaluate `dt` on `bs` in `O(height(dt))` steps (`@ByteDecisionTree.rec`,
zero `._unsafe_rec`). -/
@[expose] noncomputable def ByteDecisionTree.eval (dt : ByteDecisionTree)
    (bs : List UInt8) : Option Nat :=
  @ByteDecisionTree.rec (fun _ => List UInt8 → Option Nat)
    (fun _ => none)
    (fun expected _ => some expected)
    (fun pos thr _ _ evalLt evalGe bytes =>
      if Nat.blt (byteCodeAt bytes pos) thr then evalLt bytes else evalGe bytes)
    (fun thr _ _ evalLt evalGe bytes =>
      if Nat.blt (Trusted.MirSemantics.byteListTag 1 0 bytes) thr then
        evalLt bytes
      else evalGe bytes)
    (fun pivot _ _ evalLe evalGt bytes =>
      if byteListLe bytes pivot then evalLe bytes else evalGt bytes)
    dt bs

private theorem concat_eq_append {α : Type} :
    ∀ (xs : List α) (x : α), xs.concat x = xs ++ [x]
  | [], _ => rfl
  | y :: ys, x => congrArg (y :: ·) (concat_eq_append ys x)

private theorem toByteArray_loop_eq :
    ∀ (bs : List UInt8) (acc : ByteArray),
      (List.toByteArray.loop bs acc).data.toList = acc.data.toList ++ bs
  | [], acc => by
    change acc.data.toList = acc.data.toList ++ []
    rw [List.append_nil]
  | b :: bs, acc => by
    cases acc with
    | mk arr =>
      cases arr with
      | mk xs =>
        change (List.toByteArray.loop bs ⟨⟨xs.concat b⟩⟩).data.toList =
          xs ++ (b :: bs)
        rw [toByteArray_loop_eq bs ⟨⟨xs.concat b⟩⟩]
        change xs.concat b ++ bs = xs ++ (b :: bs)
        rw [concat_eq_append, List.append_assoc]
        rfl

/-- Closed-form UTF-8 byte-list bypass for `_root_.String.ofList cs`:
eliminates quadratic `O(L²)` `List.toByteArray.loop` (`Array.push` /
`List.concat`) unfolding so `Body.identity` strings of arbitrary length (`100+`
chars on verbatim `zerocopy` trait impls) stay well within
`defaultMaxRecDepth = 512`. -/
theorem string_ofList_bytes_eq (cs : List Char) :
    (String.ofList cs).toByteArray.data.toList =
      List.flatMap String.utf8EncodeChar cs :=
  toByteArray_loop_eq (List.flatMap String.utf8EncodeChar cs) ByteArray.empty

/-- Non-emptiness of `String.ofList cs` from non-emptiness of its UTF-8
byte list (`0` `List.toByteArray.loop` unfolding). -/
theorem not_stringBeq_empty_of_ofList {cs : List Char}
    (hId : (!List.beq (List.flatMap String.utf8EncodeChar cs) []) = true) :
    (!Trusted.MirSemantics.stringBeq (String.ofList cs) "") = true := by
  unfold Trusted.MirSemantics.stringBeq
  rw [string_ofList_bytes_eq]
  exact hId

/-- Total byte-list non-emptiness check and `ByteDecisionTree` lookup on
`b.identity`. -/
@[expose] noncomputable def checkBodyIdentityAt (dt : ByteDecisionTree)
    (idx : Nat) (b : Body) : Bool :=
  (!Trusted.MirSemantics.stringIsEmpty b.identity) &&
    match ByteDecisionTree.eval dt b.identity.toByteArray.data.toList with
    | some r => Nat.beq r idx
    | none => false

/-- Fast `checkBodyIdentityAt` introduction for
`b.identity = _root_.String.ofList cs`, bypassing `List.toByteArray.loop`
(`O(L)` linear depth instead of `O(L²)`). -/
theorem checkBodyIdentityAt_of_ofList {dt : ByteDecisionTree} {idx : Nat}
    {b : Body} {cs : List Char}
    (hEq : b.identity = String.ofList cs)
    (hFast : ((!List.beq (List.flatMap String.utf8EncodeChar cs) []) &&
      match ByteDecisionTree.eval dt (List.flatMap String.utf8EncodeChar cs)
      with
      | some r => Nat.beq r idx
      | none => false) = true) :
    checkBodyIdentityAt dt idx b = true := by
  unfold checkBodyIdentityAt Trusted.MirSemantics.stringIsEmpty
  rw [hEq, string_ofList_bytes_eq]
  cases hFlat : List.flatMap String.utf8EncodeChar cs with
  | nil =>
    rw [hFlat] at hFast
    nomatch hFast
  | cons _ _ =>
    rw [hFlat] at hFast
    exact hFast

private theorem uint8_eq_of_nat_eq {a b : UInt8} (h : a.toNat = b.toNat) :
    a = b := by
  cases a with
  | ofBitVec bvA =>
    cases b with
    | ofBitVec bvB =>
      cases bvA with
      | ofFin fA =>
        cases bvB with
        | ofFin fB =>
          cases fA
          cases fB
          dsimp only [UInt8.toNat, BitVec.toNat] at h
          subst h
          rfl

private theorem byteCmp_eq_iff {a b : UInt8} :
    Trusted.MirSemantics.byteCmp a b = .eq → a = b := by
  intro hCmp
  unfold Trusted.MirSemantics.byteCmp at hCmp
  cases hLt1 : Nat.blt a.toNat b.toNat with
  | true =>
    rw [hLt1] at hCmp
    nomatch hCmp
  | false =>
    rw [hLt1] at hCmp
    cases hLt2 : Nat.blt b.toNat a.toNat with
    | true =>
      rw [hLt2] at hCmp
      nomatch hCmp
    | false =>
      have hGe1 : b.toNat ≤ a.toNat := BinChunkTree.le_of_blt_false hLt1
      have hGe2 : a.toNat ≤ b.toNat := BinChunkTree.le_of_blt_false hLt2
      exact uint8_eq_of_nat_eq (Nat.le_antisymm hGe2 hGe1)

private theorem byteListCmp_eq_of_eq :
    ∀ {xs ys : List UInt8},
      Trusted.MirSemantics.byteListCmp xs ys = .eq → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by nomatch h
  | _ :: _, [], h => by nomatch h
  | x :: xs, y :: ys, h => by
    unfold Trusted.MirSemantics.byteListCmp at h
    cases hxy : Trusted.MirSemantics.byteCmp x y with
    | lt => rw [hxy] at h; nomatch h
    | gt => rw [hxy] at h; nomatch h
    | eq =>
      rw [hxy] at h
      have hx : x = y := byteCmp_eq_iff hxy
      have hxs : xs = ys := byteListCmp_eq_of_eq h
      subst hx; subst hxs
      rfl

private theorem byteListCmp8_step {a b : UInt8}
    {rest : Trusted.MirSemantics.ByteCmp}
    (h : (match Trusted.MirSemantics.byteCmp a b with
      | Trusted.MirSemantics.ByteCmp.lt => Trusted.MirSemantics.ByteCmp.lt
      | Trusted.MirSemantics.ByteCmp.gt => Trusted.MirSemantics.ByteCmp.gt
      | Trusted.MirSemantics.ByteCmp.eq => rest) =
      Trusted.MirSemantics.ByteCmp.eq) :
    a = b ∧ rest = Trusted.MirSemantics.ByteCmp.eq := by
  cases hc : Trusted.MirSemantics.byteCmp a b with
  | lt => rw [hc] at h; nomatch h
  | gt => rw [hc] at h; nomatch h
  | eq =>
    rw [hc] at h
    exact ⟨byteCmp_eq_iff hc, h⟩

private theorem byteListCmp8_eq_of_eq :
    ∀ {xs ys : List UInt8},
      Trusted.MirSemantics.byteListCmp8 xs ys = .eq → xs = ys
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: as,
    b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bs, h => by
    unfold Trusted.MirSemantics.byteListCmp8 at h
    have ⟨e1, h⟩ := byteListCmp8_step h
    have ⟨e2, h⟩ := byteListCmp8_step h
    have ⟨e3, h⟩ := byteListCmp8_step h
    have ⟨e4, h⟩ := byteListCmp8_step h
    have ⟨e5, h⟩ := byteListCmp8_step h
    have ⟨e6, h⟩ := byteListCmp8_step h
    have ⟨e7, h⟩ := byteListCmp8_step h
    have ⟨e8, h⟩ := byteListCmp8_step h
    have hRest := byteListCmp8_eq_of_eq h
    subst e1; subst e2; subst e3; subst e4
    subst e5; subst e6; subst e7; subst e8; subst hRest
    rfl
  | [], ys, h => byteListCmp_eq_of_eq h
  | [_], ys, h => byteListCmp_eq_of_eq h
  | [_, _], ys, h => byteListCmp_eq_of_eq h
  | [_, _, _], ys, h => byteListCmp_eq_of_eq h
  | [_, _, _, _], ys, h => byteListCmp_eq_of_eq h
  | [_, _, _, _, _], ys, h => byteListCmp_eq_of_eq h
  | [_, _, _, _, _, _], ys, h => byteListCmp_eq_of_eq h
  | [_, _, _, _, _, _, _], ys, h => byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [], h => byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_], h => byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _], h =>
    byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _], h =>
    byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _], h =>
    byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _], h =>
    byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _, _], h =>
    byteListCmp_eq_of_eq h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _, _, _], h =>
    byteListCmp_eq_of_eq h

private theorem identityKeyCmp_eq_bytes {a b : Trusted.MirSemantics.IdentityKey}
    (h : Trusted.MirSemantics.identityKeyCmp a b = .eq) :
    a.bytes = b.bytes := by
  unfold Trusted.MirSemantics.identityKeyCmp at h
  cases h1 : Nat.blt a.tag b.tag with
  | true => rw [h1] at h; nomatch h
  | false =>
    rw [h1] at h
    cases h2 : Nat.blt b.tag a.tag with
    | true => rw [h2] at h; nomatch h
    | false =>
      rw [h2] at h
      exact byteListCmp8_eq_of_eq h

private def rbMemBytes (bs : List UInt8) :
    Trusted.MirSemantics.IdentityRbTree → Prop :=
  @Trusted.MirSemantics.IdentityRbTree.rec (fun _ => Prop)
    False
    (fun _ _ x _ hl hr => bs = x.bytes ∨ hl ∨ hr)

private theorem rbRot_left1 {P Q R S T : Prop} :
    (P ∨ Q ∨ (S ∨ R ∨ T)) ↔ (S ∨ (P ∨ Q ∨ R) ∨ T) := by
  constructor
  · intro h
    cases h with
    | inl hP => exact Or.inr (Or.inl (Or.inl hP))
    | inr h1 =>
      cases h1 with
      | inl hQ => exact Or.inr (Or.inl (Or.inr (Or.inl hQ)))
      | inr hSRT =>
        cases hSRT with
        | inl hS => exact Or.inl hS
        | inr hRT =>
          cases hRT with
          | inl hR => exact Or.inr (Or.inl (Or.inr (Or.inr hR)))
          | inr hT => exact Or.inr (Or.inr hT)
  · intro h
    cases h with
    | inl hS => exact Or.inr (Or.inr (Or.inl hS))
    | inr h1 =>
      cases h1 with
      | inl hPQR =>
        cases hPQR with
        | inl hP => exact Or.inl hP
        | inr hQR =>
          cases hQR with
          | inl hQ => exact Or.inr (Or.inl hQ)
          | inr hR => exact Or.inr (Or.inr (Or.inr (Or.inl hR)))
      | inr hT => exact Or.inr (Or.inr (Or.inr (Or.inr hT)))

private theorem rbRot_left2 {P Q R S T U V : Prop} :
    (R ∨ (P ∨ Q ∨ S) ∨ (U ∨ T ∨ V)) ↔
      (U ∨ (P ∨ Q ∨ (R ∨ S ∨ T)) ∨ V) := by
  constructor
  · intro h
    cases h with
    | inl hR => exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hR))))
    | inr h1 =>
      cases h1 with
      | inl hPQS =>
        cases hPQS with
        | inl hP => exact Or.inr (Or.inl (Or.inl hP))
        | inr hQS =>
          cases hQS with
          | inl hQ => exact Or.inr (Or.inl (Or.inr (Or.inl hQ)))
          | inr hS =>
            exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hS)))))
      | inr hUTV =>
        cases hUTV with
        | inl hU => exact Or.inl hU
        | inr hTV =>
          cases hTV with
          | inl hT =>
            exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hT)))))
          | inr hV => exact Or.inr (Or.inr hV)
  · intro h
    cases h with
    | inl hU => exact Or.inr (Or.inr (Or.inl hU))
    | inr h1 =>
      cases h1 with
      | inl h2 =>
        cases h2 with
        | inl hP => exact Or.inr (Or.inl (Or.inl hP))
        | inr h3 =>
          cases h3 with
          | inl hQ => exact Or.inr (Or.inl (Or.inr (Or.inl hQ)))
          | inr hRST =>
            cases hRST with
            | inl hR => exact Or.inl hR
            | inr hST =>
              cases hST with
              | inl hS => exact Or.inr (Or.inl (Or.inr (Or.inr hS)))
              | inr hT => exact Or.inr (Or.inr (Or.inr (Or.inl hT)))
      | inr hV => exact Or.inr (Or.inr (Or.inr (Or.inr hV)))

private theorem rbRot_right1 {P Q R S T U V : Prop} :
    (R ∨ (P ∨ Q ∨ S) ∨ (U ∨ T ∨ V)) ↔
      (P ∨ Q ∨ (U ∨ (R ∨ S ∨ T) ∨ V)) := by
  constructor
  · intro h
    cases h with
    | inl hR => exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hR))))
    | inr h1 =>
      cases h1 with
      | inl hPQS =>
        cases hPQS with
        | inl hP => exact Or.inl hP
        | inr hQS =>
          cases hQS with
          | inl hQ => exact Or.inr (Or.inl hQ)
          | inr hS =>
            exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hS)))))
      | inr hUTV =>
        cases hUTV with
        | inl hU => exact Or.inr (Or.inr (Or.inl hU))
        | inr hTV =>
          cases hTV with
          | inl hT =>
            exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hT)))))
          | inr hV => exact Or.inr (Or.inr (Or.inr (Or.inr hV)))
  · intro h
    cases h with
    | inl hP => exact Or.inr (Or.inl (Or.inl hP))
    | inr h1 =>
      cases h1 with
      | inl hQ => exact Or.inr (Or.inl (Or.inr (Or.inl hQ)))
      | inr h2 =>
        cases h2 with
        | inl hU => exact Or.inr (Or.inr (Or.inl hU))
        | inr h3 =>
          cases h3 with
          | inl hRST =>
            cases hRST with
            | inl hR => exact Or.inl hR
            | inr hST =>
              cases hST with
              | inl hS => exact Or.inr (Or.inl (Or.inr (Or.inr hS)))
              | inr hT => exact Or.inr (Or.inr (Or.inr (Or.inl hT)))
          | inr hV => exact Or.inr (Or.inr (Or.inr (Or.inr hV)))

private theorem rbRot_right2 {P Q R S T : Prop} :
    (R ∨ (P ∨ Q ∨ S) ∨ T) ↔ (P ∨ Q ∨ (R ∨ S ∨ T)) := by
  constructor
  · intro h
    cases h with
    | inl hR => exact Or.inr (Or.inr (Or.inl hR))
    | inr h1 =>
      cases h1 with
      | inl hPQS =>
        cases hPQS with
        | inl hP => exact Or.inl hP
        | inr hQS =>
          cases hQS with
          | inl hQ => exact Or.inr (Or.inl hQ)
          | inr hS => exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
      | inr hT => exact Or.inr (Or.inr (Or.inr (Or.inr hT)))
  · intro h
    cases h with
    | inl hP => exact Or.inr (Or.inl (Or.inl hP))
    | inr h1 =>
      cases h1 with
      | inl hQ => exact Or.inr (Or.inl (Or.inr (Or.inl hQ)))
      | inr h2 =>
        cases h2 with
        | inl hR => exact Or.inl hR
        | inr hST =>
          cases hST with
          | inl hS => exact Or.inr (Or.inl (Or.inr (Or.inr hS)))
          | inr hT => exact Or.inr (Or.inr hT)

private theorem rbMemBytes_balance_right (bs : List UInt8)
    (l : Trusted.MirSemantics.IdentityRbTree)
    (x : Trusted.MirSemantics.IdentityKey)
    (r : Trusted.MirSemantics.IdentityRbTree)
    (hFallRL : ∀ (b : Trusted.MirSemantics.IdentityRbTree)
      (y : Trusted.MirSemantics.IdentityKey)
      (c : Trusted.MirSemantics.IdentityRbTree)
      (z : Trusted.MirSemantics.IdentityKey)
      (d : Trusted.MirSemantics.IdentityRbTree),
      Trusted.MirSemantics.identityRbBalance .black l x
          (.node .red (.node .red b y c) z d) =
        .node .red (.node .black l x b) y (.node .black c z d))
    (hFallRREmpty : ∀ (y : Trusted.MirSemantics.IdentityKey)
      (c : Trusted.MirSemantics.IdentityRbTree)
      (z : Trusted.MirSemantics.IdentityKey)
      (d : Trusted.MirSemantics.IdentityRbTree),
      Trusted.MirSemantics.identityRbBalance .black l x
          (.node .red .empty y (.node .red c z d)) =
        .node .red (.node .black l x .empty) y (.node .black c z d))
    (hFallRRBlack : ∀ (bl : Trusted.MirSemantics.IdentityRbTree)
      (bx : Trusted.MirSemantics.IdentityKey)
      (br : Trusted.MirSemantics.IdentityRbTree)
      (y : Trusted.MirSemantics.IdentityKey)
      (c : Trusted.MirSemantics.IdentityRbTree)
      (z : Trusted.MirSemantics.IdentityKey)
      (d : Trusted.MirSemantics.IdentityRbTree),
      Trusted.MirSemantics.identityRbBalance .black l x
          (.node .red (.node .black bl bx br) y (.node .red c z d)) =
        .node .red (.node .black l x (.node .black bl bx br)) y
          (.node .black c z d))
    (hFallPlain :
      (∀ b y c z d, r ≠ .node .red (.node .red b y c) z d) →
      (∀ b y c z d, r ≠ .node .red b y (.node .red c z d)) →
      Trusted.MirSemantics.identityRbBalance .black l x r =
        .node .black l x r) :
    rbMemBytes bs (Trusted.MirSemantics.identityRbBalance .black l x r) ↔
      bs = x.bytes ∨ rbMemBytes bs l ∨ rbMemBytes bs r := by
  cases r with
  | empty =>
    rw [hFallPlain (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h)]
    exact Iff.rfl
  | node cr rl rx rr =>
    cases cr with
    | black =>
      rw [hFallPlain (fun _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h)]
      exact Iff.rfl
    | red =>
      cases rl with
      | node crl rll rlx rlr =>
        cases crl with
        | red =>
          rw [hFallRL]
          dsimp only [rbMemBytes]
          exact rbRot_right1
        | black =>
          cases rr with
          | node crr rrl rrx rrr =>
            cases crr with
            | red =>
              rw [hFallRRBlack]
              dsimp only [rbMemBytes]
              exact rbRot_right2
            | black =>
              rw [hFallPlain
                (fun _ _ _ _ _ h => by injection h with _ h1; cases h1)
                (fun _ _ _ _ _ h => by injection h with _ _ _ h1; cases h1)]
              exact Iff.rfl
          | empty =>
            rw [hFallPlain
              (fun _ _ _ _ _ h => by injection h with _ h1; cases h1)
              (fun _ _ _ _ _ h => by injection h with _ _ _ h1; cases h1)]
            exact Iff.rfl
      | empty =>
        cases rr with
        | node crr rrl rrx rrr =>
          cases crr with
          | red =>
            rw [hFallRREmpty]
            dsimp only [rbMemBytes]
            exact rbRot_right2
          | black =>
            rw [hFallPlain
              (fun _ _ _ _ _ h => by injection h with _ h1; cases h1)
              (fun _ _ _ _ _ h => by injection h with _ _ _ h1; cases h1)]
            exact Iff.rfl
        | empty =>
          rw [hFallPlain (fun _ _ _ _ _ h => by injection h with _ h1; cases h1)
            (fun _ _ _ _ _ h => by injection h with _ _ _ h1; cases h1)]
          exact Iff.rfl

private theorem rbMemBytes_balance (bs : List UInt8)
    (c : Trusted.MirSemantics.IdentityRbColor)
    (l : Trusted.MirSemantics.IdentityRbTree)
    (x : Trusted.MirSemantics.IdentityKey)
    (r : Trusted.MirSemantics.IdentityRbTree) :
    rbMemBytes bs (Trusted.MirSemantics.identityRbBalance c l x r) ↔
      bs = x.bytes ∨ rbMemBytes bs l ∨ rbMemBytes bs r := by
  cases c with
  | red => exact Iff.rfl
  | black =>
    cases l with
    | empty =>
      exact rbMemBytes_balance_right bs .empty x r
        (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ _ _ _ _ _ => rfl) (fun h1 h2 => by
          cases r with
          | empty => rfl
          | node cr rl rx rr =>
            cases cr with
            | black => rfl
            | red =>
              cases rl with
              | empty =>
                cases rr with
                | empty => rfl
                | node crr _ _ _ =>
                  cases crr with
                  | black => rfl
                  | red => exact False.elim (h2 _ _ _ _ _ rfl)
              | node crl _ _ _ =>
                cases crl with
                | red => exact False.elim (h1 _ _ _ _ _ rfl)
                | black =>
                  cases rr with
                  | empty => rfl
                  | node crr _ _ _ =>
                    cases crr with
                    | black => rfl
                    | red => exact False.elim (h2 _ _ _ _ _ rfl))
    | node cl ll lx lr =>
      cases cl with
      | black =>
        exact rbMemBytes_balance_right bs (.node .black ll lx lr) x r
          (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
          (fun _ _ _ _ _ _ _ => rfl) (fun h1 h2 => by
            cases r with
            | empty => rfl
            | node cr rl rx rr =>
              cases cr with
              | black => rfl
              | red =>
                cases rl with
                | empty =>
                  cases rr with
                  | empty => rfl
                  | node crr _ _ _ =>
                    cases crr with
                    | black => rfl
                    | red => exact False.elim (h2 _ _ _ _ _ rfl)
                | node crl _ _ _ =>
                  cases crl with
                  | red => exact False.elim (h1 _ _ _ _ _ rfl)
                  | black =>
                    cases rr with
                    | empty => rfl
                    | node crr _ _ _ =>
                      cases crr with
                      | black => rfl
                      | red => exact False.elim (h2 _ _ _ _ _ rfl))
      | red =>
        cases ll with
        | node cll lll llx llr =>
          cases cll with
          | red =>
            dsimp only [Trusted.MirSemantics.identityRbBalance, rbMemBytes]
            exact rbRot_right2.symm
          | black =>
            cases lr with
            | node clr lrl lrx lrr =>
              cases clr with
              | red =>
                dsimp only [Trusted.MirSemantics.identityRbBalance, rbMemBytes]
                exact rbRot_left2
              | black =>
                exact rbMemBytes_balance_right bs
                  (.node .red (.node .black lll llx llr) lx
                    (.node .black lrl lrx lrr)) x r
                  (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
                  (fun _ _ _ _ _ _ _ => rfl) (fun h1 h2 => by
                    cases r with
                    | empty => rfl
                    | node cr rl rx rr =>
                      cases cr with
                      | black => rfl
                      | red =>
                        cases rl with
                        | empty =>
                          cases rr with
                          | empty => rfl
                          | node crr _ _ _ =>
                            cases crr with
                            | black => rfl
                            | red => exact False.elim (h2 _ _ _ _ _ rfl)
                        | node crl _ _ _ =>
                          cases crl with
                          | red => exact False.elim (h1 _ _ _ _ _ rfl)
                          | black =>
                            cases rr with
                            | empty => rfl
                            | node crr _ _ _ =>
                              cases crr with
                              | black => rfl
                              | red => exact False.elim (h2 _ _ _ _ _ rfl))
            | empty =>
              exact rbMemBytes_balance_right bs
                (.node .red (.node .black lll llx llr) lx .empty) x r
                (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
                (fun _ _ _ _ _ _ _ => rfl) (fun h1 h2 => by
                  cases r with
                  | empty => rfl
                  | node cr rl rx rr =>
                    cases cr with
                    | black => rfl
                    | red =>
                      cases rl with
                      | empty =>
                        cases rr with
                        | empty => rfl
                        | node crr _ _ _ =>
                          cases crr with
                          | black => rfl
                          | red => exact False.elim (h2 _ _ _ _ _ rfl)
                      | node crl _ _ _ =>
                        cases crl with
                        | red => exact False.elim (h1 _ _ _ _ _ rfl)
                        | black =>
                          cases rr with
                          | empty => rfl
                          | node crr _ _ _ =>
                            cases crr with
                            | black => rfl
                            | red => exact False.elim (h2 _ _ _ _ _ rfl))
        | empty =>
          cases lr with
          | node clr lrl lrx lrr =>
            cases clr with
            | red =>
              dsimp only [Trusted.MirSemantics.identityRbBalance, rbMemBytes]
              exact rbRot_left2
            | black =>
              exact rbMemBytes_balance_right bs
                (.node .red .empty lx (.node .black lrl lrx lrr)) x r
                (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
                (fun _ _ _ _ _ _ _ => rfl) (fun h1 h2 => by
                  cases r with
                  | empty => rfl
                  | node cr rl rx rr =>
                    cases cr with
                    | black => rfl
                    | red =>
                      cases rl with
                      | empty =>
                        cases rr with
                        | empty => rfl
                        | node crr _ _ _ =>
                          cases crr with
                          | black => rfl
                          | red => exact False.elim (h2 _ _ _ _ _ rfl)
                      | node crl _ _ _ =>
                        cases crl with
                        | red => exact False.elim (h1 _ _ _ _ _ rfl)
                        | black =>
                          cases rr with
                          | empty => rfl
                          | node crr _ _ _ =>
                            cases crr with
                            | black => rfl
                            | red => exact False.elim (h2 _ _ _ _ _ rfl))
          | empty =>
            exact rbMemBytes_balance_right bs (.node .red .empty lx .empty) x r
              (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
              (fun _ _ _ _ _ _ _ => rfl) (fun h1 h2 => by
                cases r with
                | empty => rfl
                | node cr rl rx rr =>
                  cases cr with
                  | black => rfl
                  | red =>
                    cases rl with
                    | empty =>
                      cases rr with
                      | empty => rfl
                      | node crr _ _ _ =>
                        cases crr with
                        | black => rfl
                        | red => exact False.elim (h2 _ _ _ _ _ rfl)
                    | node crl _ _ _ =>
                      cases crl with
                      | red => exact False.elim (h1 _ _ _ _ _ rfl)
                      | black =>
                        cases rr with
                        | empty => rfl
                        | node crr _ _ _ =>
                          cases crr with
                          | black => rfl
                          | red => exact False.elim (h2 _ _ _ _ _ rfl))

private theorem rbInsertAux_of_not_mem (k : Trusted.MirSemantics.IdentityKey)
    (tr : Trusted.MirSemantics.IdentityRbTree)
    (hNot : ¬ rbMemBytes k.bytes tr) :
    ∃ tr' : Trusted.MirSemantics.IdentityRbTree,
      Trusted.MirSemantics.identityRbInsertAux k tr = some tr' ∧
      ∀ bs : List UInt8,
        rbMemBytes bs tr' ↔ bs = k.bytes ∨ rbMemBytes bs tr := by
  induction tr with
  | empty =>
    refine ⟨.node .red .empty k .empty, rfl, fun bs => ?_⟩
    constructor
    · intro h
      cases h with
      | inl hEq => exact Or.inl hEq
      | inr hOr =>
        cases hOr with
        | inl hF => exact False.elim hF
        | inr hF => exact False.elim hF
    · intro h
      cases h with
      | inl hEq => exact Or.inl hEq
      | inr hF => exact False.elim hF
  | node c l x r ihL ihR =>
    have hNx : k.bytes ≠ x.bytes := fun h => hNot (Or.inl h)
    have hNl : ¬ rbMemBytes k.bytes l := fun h => hNot (Or.inr (Or.inl h))
    have hNr : ¬ rbMemBytes k.bytes r := fun h => hNot (Or.inr (Or.inr h))
    cases hCmp : Trusted.MirSemantics.identityKeyCmp k x with
    | eq => exact False.elim (hNx (identityKeyCmp_eq_bytes hCmp))
    | lt =>
      let ⟨l', hlEq, hlMem⟩ := ihL hNl
      have hIns : Trusted.MirSemantics.identityRbInsertAux k (.node c l x r) =
          some (Trusted.MirSemantics.identityRbBalance c l' x r) := by
        change (match Trusted.MirSemantics.identityKeyCmp k x with
          | .lt => match Trusted.MirSemantics.identityRbInsertAux k l with
            | none => none
            | some l' => some (Trusted.MirSemantics.identityRbBalance c l' x r)
          | .eq => none
          | .gt => match Trusted.MirSemantics.identityRbInsertAux k r with
            | none => none
            | some r' =>
              some (Trusted.MirSemantics.identityRbBalance c l x r')) =
          _
        rw [hCmp, hlEq]
      refine ⟨Trusted.MirSemantics.identityRbBalance c l' x r, hIns,
        fun bs => ?_⟩
      rw [rbMemBytes_balance bs c l' x r, hlMem bs]
      constructor
      · intro h
        cases h with
        | inl hX => exact Or.inr (Or.inl hX)
        | inr h1 =>
          cases h1 with
          | inl hKL =>
            cases hKL with
            | inl hK => exact Or.inl hK
            | inr hL => exact Or.inr (Or.inr (Or.inl hL))
          | inr hR => exact Or.inr (Or.inr (Or.inr hR))
      · intro h
        cases h with
        | inl hK => exact Or.inr (Or.inl (Or.inl hK))
        | inr h1 =>
          cases h1 with
          | inl hX => exact Or.inl hX
          | inr h2 =>
            cases h2 with
            | inl hL => exact Or.inr (Or.inl (Or.inr hL))
            | inr hR => exact Or.inr (Or.inr hR)
    | gt =>
      let ⟨r', hrEq, hrMem⟩ := ihR hNr
      have hIns : Trusted.MirSemantics.identityRbInsertAux k (.node c l x r) =
          some (Trusted.MirSemantics.identityRbBalance c l x r') := by
        change (match Trusted.MirSemantics.identityKeyCmp k x with
          | .lt => match Trusted.MirSemantics.identityRbInsertAux k l with
            | none => none
            | some l' => some (Trusted.MirSemantics.identityRbBalance c l' x r)
          | .eq => none
          | .gt => match Trusted.MirSemantics.identityRbInsertAux k r with
            | none => none
            | some r' =>
              some (Trusted.MirSemantics.identityRbBalance c l x r')) =
          _
        rw [hCmp, hrEq]
      refine ⟨Trusted.MirSemantics.identityRbBalance c l x r', hIns,
        fun bs => ?_⟩
      rw [rbMemBytes_balance bs c l x r', hrMem bs]
      constructor
      · intro h
        cases h with
        | inl hX => exact Or.inr (Or.inl hX)
        | inr h1 =>
          cases h1 with
          | inl hL => exact Or.inr (Or.inr (Or.inl hL))
          | inr hKR =>
            cases hKR with
            | inl hK => exact Or.inl hK
            | inr hR => exact Or.inr (Or.inr (Or.inr hR))
      · intro h
        cases h with
        | inl hK => exact Or.inr (Or.inr (Or.inl hK))
        | inr h1 =>
          cases h1 with
          | inl hX => exact Or.inl hX
          | inr h2 =>
            cases h2 with
            | inl hL => exact Or.inr (Or.inl hL)
            | inr hR => exact Or.inr (Or.inr (Or.inr hR))

private theorem rbInsert_of_not_mem (k : Trusted.MirSemantics.IdentityKey)
    (tr : Trusted.MirSemantics.IdentityRbTree)
    (hNot : ¬ rbMemBytes k.bytes tr) :
    ∃ tr' : Trusted.MirSemantics.IdentityRbTree,
      Trusted.MirSemantics.identityRbInsert k tr = some tr' ∧
      ∀ bs : List UInt8,
        rbMemBytes bs tr' ↔ bs = k.bytes ∨ rbMemBytes bs tr := by
  let ⟨trAux, hAuxEq, hAuxMem⟩ := rbInsertAux_of_not_mem k tr hNot
  cases trAux with
  | empty =>
    have hIns : Trusted.MirSemantics.identityRbInsert k tr = some .empty := by
      unfold Trusted.MirSemantics.identityRbInsert
      rw [hAuxEq]
    exact ⟨.empty, hIns, hAuxMem⟩
  | node _ l x r =>
    have hIns : Trusted.MirSemantics.identityRbInsert k tr =
        some (.node .black l x r) := by
      unfold Trusted.MirSemantics.identityRbInsert
      rw [hAuxEq]
    exact ⟨.node .black l x r, hIns, hAuxMem⟩

private theorem ne_0_of_succ (k : Nat) : 0 ≠ k + 1 :=
  fun h => by cases h

private theorem ne_succ {a b : Nat} (h : a ≠ b) : a + 1 ≠ b + 1 :=
  fun hEq => h (Nat.succ.inj hEq)

private theorem lt_add_left_of_lt {a b k : Nat} (h : a < b) : a < k + b :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left b k)

private theorem rbInsertBody_of_valid (b : Body)
    (tr : Trusted.MirSemantics.IdentityRbTree)
    (hNonEmpty : b.identity.toByteArray.data.toList ≠ [])
    (hNot : ¬ rbMemBytes b.identity.toByteArray.data.toList tr) :
    ∃ tr' : Trusted.MirSemantics.IdentityRbTree,
      Trusted.MirSemantics.identityRbInsertBody b tr = some tr' ∧
      ∀ bs : List UInt8,
        rbMemBytes bs tr' ↔
          bs = b.identity.toByteArray.data.toList ∨ rbMemBytes bs tr := by
  cases hBytes : b.identity.toByteArray.data.toList with
  | nil => exact False.elim (hNonEmpty hBytes)
  | cons u us =>
    have hNot' :
        ¬ rbMemBytes
          (⟨Trusted.MirSemantics.byteListTag 1 0 (u :: us), u :: us⟩ :
            Trusted.MirSemantics.IdentityKey).bytes tr := by
      change ¬ rbMemBytes (u :: us) tr
      rw [← hBytes]
      exact hNot
    let ⟨tr', hEq, hMem⟩ :=
      rbInsert_of_not_mem
        ⟨Trusted.MirSemantics.byteListTag 1 0 (u :: us), u :: us⟩ tr hNot'
    have hBodyEq :
        Trusted.MirSemantics.identityRbInsertBody b tr = some tr' := by
      unfold Trusted.MirSemantics.identityRbInsertBody
      rw [hBytes]
      exact hEq
    refine ⟨tr', hBodyEq, fun bs => ?_⟩
    exact hMem bs

private theorem getElem?_map_body_bytes {f : List UInt8 → Option Nat}
    {bs : List Body} {base : Nat} :
    ∀ {k1 k2 : Nat} {b1 b2 : Body},
      (∀ k b, Trusted.MirSemantics.getElem? bs k = some b →
        b.identity.toByteArray.data.toList ≠ [] ∧
        f b.identity.toByteArray.data.toList = some (base + k)) →
      Trusted.MirSemantics.getElem? bs k1 = some b1 →
      Trusted.MirSemantics.getElem? bs k2 = some b2 →
      k1 ≠ k2 →
      b1.identity.toByteArray.data.toList ≠
        b2.identity.toByteArray.data.toList := by
  intro k1 k2 b1 b2 hf h1 h2 hne hEq
  have hF1 := (hf k1 b1 h1).2
  have hF2 := (hf k2 b2 h2).2
  rw [hEq, hF2] at hF1
  injection hF1 with hk
  exact hne (Nat.add_left_cancel hk).symm

private theorem bodiesHaveUniqueIdentitiesAux_of_inj
    {f : List UInt8 → Option Nat} :
    ∀ (xs : List Body) (base : Nat) (tr : Trusted.MirSemantics.IdentityRbTree),
      (∀ k b, Trusted.MirSemantics.getElem? xs k = some b →
        b.identity.toByteArray.data.toList ≠ [] ∧
        f b.identity.toByteArray.data.toList = some (base + k)) →
      (∀ k b, Trusted.MirSemantics.getElem? xs k = some b →
        ¬ rbMemBytes b.identity.toByteArray.data.toList tr) →
      Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux xs tr = true
  | [], _, _, _, _ => rfl
  | [b1], base, tr, hInj, hFresh => by
    unfold Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux
    have h1 := rbInsertBody_of_valid b1 tr (hInj 0 b1 rfl).1 (hFresh 0 b1 rfl)
    let ⟨tr1, hEq1, _⟩ := h1
    rw [hEq1]
    rfl
  | [b1, b2], base, tr, hInj, hFresh => by
    unfold Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux
    let ⟨tr1, hEq1, hMem1⟩ :=
      rbInsertBody_of_valid b1 tr (hInj 0 b1 rfl).1 (hFresh 0 b1 rfl)
    have hNe12 :=
      getElem?_map_body_bytes hInj (k1 := 0) (k2 := 1) rfl rfl (ne_0_of_succ 0)
    have hFresh2 : ¬ rbMemBytes b2.identity.toByteArray.data.toList tr1 := by
      rw [hMem1]
      intro hOr
      cases hOr with
      | inl hEq => exact hNe12.symm hEq
      | inr hIn => exact hFresh 1 b2 rfl hIn
    let ⟨tr2, hEq2, _⟩ :=
      rbInsertBody_of_valid b2 tr1 (hInj 1 b2 rfl).1 hFresh2
    rw [hEq1]
    change (Trusted.MirSemantics.identityRbInsertBody b2 tr1).isSome = true
    rw [hEq2]
    rfl
  | [b1, b2, b3], base, tr, hInj, hFresh => by
    unfold Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux
    let ⟨tr1, hEq1, hMem1⟩ :=
      rbInsertBody_of_valid b1 tr (hInj 0 b1 rfl).1 (hFresh 0 b1 rfl)
    have hNe12 :=
      getElem?_map_body_bytes hInj (k1 := 0) (k2 := 1) rfl rfl (ne_0_of_succ 0)
    have hNe13 :=
      getElem?_map_body_bytes hInj (k1 := 0) (k2 := 2) rfl rfl (ne_0_of_succ 1)
    have hNe23 :=
      getElem?_map_body_bytes hInj (k1 := 1) (k2 := 2) rfl rfl
        (ne_succ (ne_0_of_succ 0))
    have hFresh2 : ¬ rbMemBytes b2.identity.toByteArray.data.toList tr1 := by
      rw [hMem1]
      intro hOr
      cases hOr with
      | inl hEq => exact hNe12.symm hEq
      | inr hIn => exact hFresh 1 b2 rfl hIn
    let ⟨tr2, hEq2, hMem2⟩ :=
      rbInsertBody_of_valid b2 tr1 (hInj 1 b2 rfl).1 hFresh2
    have hFresh3 : ¬ rbMemBytes b3.identity.toByteArray.data.toList tr2 := by
      rw [hMem2, hMem1]
      intro hOr
      cases hOr with
      | inl hEq => exact hNe23.symm hEq
      | inr h1 =>
        cases h1 with
        | inl hEq => exact hNe13.symm hEq
        | inr hIn => exact hFresh 2 b3 rfl hIn
    let ⟨tr3, hEq3, _⟩ := rbInsertBody_of_valid b3 tr2 (hInj 2 b3 rfl).1 hFresh3
    rw [hEq1]
    change (Trusted.MirSemantics.identityRbInsertBodyOpt b3
      (Trusted.MirSemantics.identityRbInsertBody b2 tr1)).isSome = true
    rw [hEq2]
    change (Trusted.MirSemantics.identityRbInsertBody b3 tr2).isSome = true
    rw [hEq3]
    rfl
  | b1 :: b2 :: b3 :: b4 :: rest, base, tr, hInj, hFresh => by
    unfold Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux
    let ⟨tr1, hEq1, hMem1⟩ :=
      rbInsertBody_of_valid b1 tr (hInj 0 b1 rfl).1 (hFresh 0 b1 rfl)
    have hNe12 :=
      getElem?_map_body_bytes hInj (k1 := 0) (k2 := 1) rfl rfl (ne_0_of_succ 0)
    have hNe13 :=
      getElem?_map_body_bytes hInj (k1 := 0) (k2 := 2) rfl rfl (ne_0_of_succ 1)
    have hNe14 :=
      getElem?_map_body_bytes hInj (k1 := 0) (k2 := 3) rfl rfl (ne_0_of_succ 2)
    have hNe23 :=
      getElem?_map_body_bytes hInj (k1 := 1) (k2 := 2) rfl rfl
        (ne_succ (ne_0_of_succ 0))
    have hNe24 :=
      getElem?_map_body_bytes hInj (k1 := 1) (k2 := 3) rfl rfl
        (ne_succ (ne_0_of_succ 1))
    have hNe34 :=
      getElem?_map_body_bytes hInj (k1 := 2) (k2 := 3) rfl rfl
        (ne_succ (ne_succ (ne_0_of_succ 0)))
    have hFresh2 : ¬ rbMemBytes b2.identity.toByteArray.data.toList tr1 := by
      rw [hMem1]
      intro hOr
      cases hOr with
      | inl hEq => exact hNe12.symm hEq
      | inr hIn => exact hFresh 1 b2 rfl hIn
    let ⟨tr2, hEq2, hMem2⟩ :=
      rbInsertBody_of_valid b2 tr1 (hInj 1 b2 rfl).1 hFresh2
    have hFresh3 : ¬ rbMemBytes b3.identity.toByteArray.data.toList tr2 := by
      rw [hMem2, hMem1]
      intro hOr
      cases hOr with
      | inl hEq => exact hNe23.symm hEq
      | inr h1 =>
        cases h1 with
        | inl hEq => exact hNe13.symm hEq
        | inr hIn => exact hFresh 2 b3 rfl hIn
    let ⟨tr3, hEq3, hMem3⟩ :=
      rbInsertBody_of_valid b3 tr2 (hInj 2 b3 rfl).1 hFresh3
    have hFresh4 : ¬ rbMemBytes b4.identity.toByteArray.data.toList tr3 := by
      rw [hMem3, hMem2, hMem1]
      intro hOr
      cases hOr with
      | inl hEq => exact hNe34.symm hEq
      | inr h1 =>
        cases h1 with
        | inl hEq => exact hNe24.symm hEq
        | inr h2 =>
          cases h2 with
          | inl hEq => exact hNe14.symm hEq
          | inr hIn => exact hFresh 3 b4 rfl hIn
    let ⟨tr4, hEq4, hMem4⟩ :=
      rbInsertBody_of_valid b4 tr3 (hInj 3 b4 rfl).1 hFresh4
    rw [hEq1]
    change (match Trusted.MirSemantics.identityRbInsertBodyOpt b4
      (Trusted.MirSemantics.identityRbInsertBodyOpt b3
        (Trusted.MirSemantics.identityRbInsertBody b2 tr1)) with
      | none => false
      | some t' =>
        Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux rest t') = true
    rw [hEq2]
    change (match Trusted.MirSemantics.identityRbInsertBodyOpt b4
      (Trusted.MirSemantics.identityRbInsertBody b3 tr2) with
      | none => false
      | some t' =>
        Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux rest t') = true
    rw [hEq3]
    change (match Trusted.MirSemantics.identityRbInsertBody b4 tr3 with
      | none => false
      | some t' =>
        Trusted.MirSemantics.bodiesHaveUniqueIdentitiesAux rest t') = true
    rw [hEq4]
    dsimp only
    refine bodiesHaveUniqueIdentitiesAux_of_inj (f := f) rest (base + 4) tr4
      ?_ ?_
    · intro k b hk
      have hSub := hInj (k + 4) b hk
      have hAssoc : base + (k + 4) = base + 4 + k := by
        rw [Nat.add_assoc, Nat.add_comm k 4, ← Nat.add_assoc]
      rw [← hAssoc]
      exact hSub
    · intro k b hk
      rw [hMem4, hMem3, hMem2, hMem1]
      intro hOr
      cases hOr with
      | inl hEq =>
        exact getElem?_map_body_bytes hInj (k1 := 3) (k2 := k + 4) rfl hk
          (Nat.ne_of_lt (lt_add_left_of_lt (Nat.lt_succ_self 3))) hEq.symm
      | inr h1 =>
        cases h1 with
        | inl hEq =>
          exact getElem?_map_body_bytes hInj (k1 := 2) (k2 := k + 4) rfl hk
            (Nat.ne_of_lt (lt_add_left_of_lt
              (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))))
            hEq.symm
        | inr h2 =>
          cases h2 with
          | inl hEq =>
            exact getElem?_map_body_bytes hInj (k1 := 1) (k2 := k + 4) rfl hk
              (Nat.ne_of_lt (lt_add_left_of_lt
                (Nat.lt_trans (Nat.lt_succ_self 1)
                  (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)))))
              hEq.symm
          | inr h3 =>
            cases h3 with
            | inl hEq =>
              exact getElem?_map_body_bytes hInj (k1 := 0) (k2 := k + 4) rfl hk
                (ne_0_of_succ (k + 3)) hEq.symm
            | inr hIn => exact hFresh (k + 4) b hk hIn

/-- Soundness of `ByteDecisionTree` uniqueness certificate: an `O(N log N)`
check over `BinChunkTree` implies
`Trusted.MirSemantics.bodiesHaveUniqueIdentities` on `BinChunkTree.toList t`. -/
theorem bodiesHaveUniqueIdentities_of_decisionTree
    {t : BinChunkTree Body} (dt : ByteDecisionTree)
    (hwf : BinChunkTree.wf t = true)
    (hCheck : BinChunkTree.allIdx (checkBodyIdentityAt dt) t 0 = true) :
    Trusted.MirSemantics.bodiesHaveUniqueIdentities (BinChunkTree.toList t) =
      true := by
  have hPointwise : ∀ (k : Nat) (b : Body),
      Trusted.MirSemantics.getElem? (BinChunkTree.toList t) k = some b →
      b.identity.toByteArray.data.toList ≠ [] ∧
      ByteDecisionTree.eval dt b.identity.toByteArray.data.toList =
        some (0 + k) := by
    intro k b hGet
    rw [BinChunkTree.getElem?_toList_eq_get? hwf k] at hGet
    have hAt := BinChunkTree.allIdx_get? hwf hCheck hGet
    rw [Nat.zero_add] at hAt
    unfold checkBodyIdentityAt at hAt
    cases hNe : (!Trusted.MirSemantics.stringIsEmpty b.identity) with
    | false =>
      rw [hNe] at hAt
      nomatch hAt
    | true =>
      rw [hNe] at hAt
      cases hEval :
          ByteDecisionTree.eval dt b.identity.toByteArray.data.toList with
      | none =>
        rw [hEval] at hAt
        nomatch hAt
      | some r =>
        rw [hEval] at hAt
        have hr : r = k := Nat.eq_of_beq_eq_true hAt
        subst hr
        have hNonEmpty : b.identity.toByteArray.data.toList ≠ [] := by
          intro hNil
          unfold Trusted.MirSemantics.stringIsEmpty at hNe
          rw [hNil] at hNe
          nomatch hNe
        rw [Nat.zero_add]
        exact ⟨hNonEmpty, rfl⟩
  unfold Trusted.MirSemantics.bodiesHaveUniqueIdentities
  exact bodiesHaveUniqueIdentitiesAux_of_inj (BinChunkTree.toList t) 0 .empty
    hPointwise (fun _ _ _ hFalse => hFalse)

/-! ## 3. Shard-Local Verification & Zero-Coupling Crate Lift -/

/-- Intrinsic static admission of a single call-free `Body` (independent of
`Program`). -/
@[expose] noncomputable def BodyStaticIntrinsic (body : Body) : Bool :=
  (!Trusted.MirSemantics.stringIsEmpty body.identity) &&
    (!body.basicBlocks.isEmpty) &&
    Nat.blt body.argumentCount body.locals.length &&
    Trusted.MirSemantics.storageAnnotationsInBounds body &&
    Trusted.MirSemantics.discriminantTypesValid body &&
    Trusted.MirSemantics.castTypesValid body &&
    Trusted.MirSemantics.assertConditionTypesValid body &&
    body.locals.all Trusted.MirSemantics.isSupportedScalarOrUnitTy &&
    (!Trusted.MirSemantics.bodyHasAnyCall body)

/-- Fast `BodyStaticIntrinsic` introduction for
`body.identity = _root_.String.ofList cs`, bypassing `List.toByteArray.loop`
(`O(L)` linear depth instead of `O(L²)` on `100+`-byte `zerocopy` trait-impl
paths). -/
theorem bodyStaticIntrinsic_of_ofList {body : Body} {cs : List Char}
    (hEq : body.identity = String.ofList cs)
    (hFast : ((!List.beq (List.flatMap String.utf8EncodeChar cs) []) &&
      (!body.basicBlocks.isEmpty) &&
      Nat.blt body.argumentCount body.locals.length &&
      Trusted.MirSemantics.storageAnnotationsInBounds body &&
      Trusted.MirSemantics.discriminantTypesValid body &&
      Trusted.MirSemantics.castTypesValid body &&
      Trusted.MirSemantics.assertConditionTypesValid body &&
      body.locals.all Trusted.MirSemantics.isSupportedScalarOrUnitTy &&
      (!Trusted.MirSemantics.bodyHasAnyCall body)) = true) :
    BodyStaticIntrinsic body = true := by
  unfold BodyStaticIntrinsic Trusted.MirSemantics.stringIsEmpty
  rw [hEq, string_ofList_bytes_eq]
  cases hFlat : List.flatMap String.utf8EncodeChar cs with
  | nil =>
    rw [hFlat] at hFast
    nomatch hFast
  | cons _ _ =>
    rw [hFlat] at hFast
    exact hFast

/-- Shard-local verification obligation for a single `Body`, completely
decoupled from `Captured.program` and global `DefId` numbering. -/
@[expose] def LocalBodyVerified (body : Body) (safetyPre : List Val → Prop) :
    Prop :=
  BodyStaticIntrinsic body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    (body.isUnsafe = true → safetyPre args) →
    Safe body args

/-- Introduce `LocalBodyVerified` for an arbitrary `Body` from static admission
and `Safe`. -/
theorem localBodyVerified_intro {body : Body} {safetyPre : List Val → Prop}
    (hAdm : BodyStaticIntrinsic body = true)
    (hSafe : ∀ args : List Val,
      ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      Safe body args) :
    LocalBodyVerified body safetyPre :=
  ⟨hAdm, hSafe⟩

/-- Introduce `LocalBodyVerified` from a deterministic fuel-bounded `Runs`
certificate on zero-argument unit/scalar functions (`0` `Program` coupling). -/
theorem localBodyVerified_of_runs0 {body : Body} {safetyPre : List Val → Prop}
    {fuel : Nat} {ret : Val}
    (hAdm : BodyStaticIntrinsic body = true)
    (hTys : (body.locals.drop 1).take body.argumentCount = [])
    (hRuns : Runs body fuel [] ret) :
    LocalBodyVerified body safetyPre := by
  refine ⟨hAdm, fun args valid _ => ?_⟩
  have hMatch : checkArgsMatch args [] = true := by
    unfold ValidEntryArgs at valid
    rw [hTys] at valid
    exact valid
  have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
  subst hNil
  exact (run_initial_success hRuns).1

/-- Introduce `LocalBodyVerified` for a 1-argument function of type `argTy`
from a universal single-argument `Executes` certificate (`0` `Program`
coupling). -/
theorem localBodyVerified_of_executes1 {body : Body}
    {safetyPre : List Val → Prop} {argTy : MirTy} {retFn : Val → Val}
    (hAdm : BodyStaticIntrinsic body = true)
    (hTys : (body.locals.drop 1).take body.argumentCount = [argTy])
    (hExec : ∀ {v : Val}, checkVal v argTy = true →
      Executes body (mkState 0 0 (initLocalsLoop body [v] 0 body.locals))
        (retFn v)) :
    LocalBodyVerified body safetyPre := by
  refine ⟨hAdm, fun args valid _ => ?_⟩
  have hMatch : checkArgsMatch args [argTy] = true := by
    unfold ValidEntryArgs at valid
    rw [hTys] at valid
    exact valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (hExec hv)

/-- Introduce `LocalBodyVerified` for a 1-argument function of type `argTy`
from a universal single-argument fuel-bounded `Runs` certificate. -/
theorem localBodyVerified_of_runs1 {body : Body}
    {safetyPre : List Val → Prop} {argTy : MirTy} {fuel : Nat}
    {retFn : Val → Val}
    (hAdm : BodyStaticIntrinsic body = true)
    (hTys : (body.locals.drop 1).take body.argumentCount = [argTy])
    (hRuns : ∀ v : Val, checkVal v argTy = true →
      Runs body fuel [v] (retFn v)) :
    LocalBodyVerified body safetyPre :=
  localBodyVerified_of_executes1 hAdm hTys (fun hv => run_executes (hRuns _ hv))

/-- Introduce `LocalBodyVerified` for a 1-argument `.unit` function from a
deterministic `Runs` certificate (`<() as PointerMetadata>::to_elem_count`). -/
theorem localBodyVerified_of_runs_unit1 {body : Body}
    {safetyPre : List Val → Prop} {fuel : Nat} {ret : Val}
    (hAdm : BodyStaticIntrinsic body = true)
    (hTys : (body.locals.drop 1).take body.argumentCount = [.unit])
    (hRuns : Runs body fuel [.unit] ret) :
    LocalBodyVerified body safetyPre := by
  refine localBodyVerified_of_runs1 (fuel := fuel) (retFn := fun _ => ret)
    hAdm hTys (fun v hv => ?_)
  have hU : v = .unit := checkVal_unit_iff.mp hv
  subst hU
  exact hRuns

private theorem writePlace_isize_copy {v : Val}
    (hv : checkVal v (.int .isize false) = true) :
    writePlace [.immediate none, .immediate (some v)] entryMemory 0
        (.int .isize false) v =
      .ok ([.immediate (some v), .immediate (some v)], entryMemory) := by
  unfold writePlace
  rw [hv]
  rfl

/-- Introduce `LocalBodyVerified` for a 1-argument `usize` copy-return identity
function (`<usize as PointerMetadata>::{from,to}_elem_count`). -/
theorem localBodyVerified_isize_identity {body : Body}
    {safetyPre : List Val → Prop}
    (hAdm : BodyStaticIntrinsic body = true)
    (hTys : (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (hLoc : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (hRval : ∀ v : Val, evalRvalue body.locals
      [.immediate none, .immediate (some v)]
      entryMemory (.int .isize false) (.use (.copy ⟨1, []⟩)) =
      .ok (v, [.immediate none, .immediate (some v)], entryMemory))
    (hStep : ∀ v : Val, evalStep (bodyProg body) 0
      (mkState 0 0 [.immediate none, .immediate (some v)]) =
      match evalRvalue body.locals
          [.immediate none, .immediate (some v)]
          entryMemory (.int .isize false) (.use (.copy ⟨1, []⟩)) with
      | .error k => .fault k
      | .ok (val, l1, m1) =>
        match writePlace l1 m1 0 (.int .isize false) val with
        | .error k => .fault k
        | .ok (l2, m2) =>
          .step { frames :=
                    [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := l2 }],
                  callerMem := ⟨[]⟩, mem := m2 })
    (hRet : ∀ v : Val, evalStep (bodyProg body) 0
      (mkState 0 1 [.immediate (some v), .immediate (some v)]) =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    LocalBodyVerified body safetyPre := by
  refine localBodyVerified_of_executes1 (retFn := fun v => v) hAdm hTys
    (fun {v} hv => ?_)
  have h1 : evalStep (bodyProg body) 0
      (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) =
      .step (mkState 0 1 [.immediate (some v), .immediate (some v)]) := by
    rw [hLoc v, hStep v, hRval v]
    dsimp only
    rw [writePlace_isize_copy hv]
    rfl
  exact .next h1 (.ret (hRet v))

/-- Tree-structured shard/crate conjunction of `LocalBodyVerified` obligations
(`0` `._unsafe_rec`, depth `O(log N)`, zero `Captured.program` dependency). -/
@[expose] def TreeLocalVerified (specs : Specs) (t : BinChunkTree Body) :
    Prop :=
  @BinChunkTree.rec Body (fun _ => Prop)
    True
    (fun body => LocalBodyVerified body (specs.safety body.identity))
    (fun _ _ _ pL pR => pL ∧ pR)
    t

/-- Extract `LocalBodyVerified` at any `BinChunkTree.get? t idx = some body` in
`O(log N)` logical depth. -/
theorem treeLocalVerified_get? {specs : Specs} :
    ∀ {t : BinChunkTree Body},
      BinChunkTree.wf t = true →
      TreeLocalVerified specs t →
      ∀ {idx : Nat} {body : Body},
        BinChunkTree.get? t idx = some body →
        LocalBodyVerified body (specs.safety body.identity) := by
  intro t
  induction t with
  | empty =>
    intro _ _ _ _ hGet
    nomatch hGet
  | leaf b =>
    intro _ hLoc idx body hGet
    dsimp only [BinChunkTree.get?] at hGet
    cases idx with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact hLoc
    | succ _ =>
      nomatch hGet
  | branch half l r ihL ihR =>
    intro hwf hLoc idx body hGet
    change (Nat.beq (BinChunkTree.size l) half &&
      (BinChunkTree.wf l && BinChunkTree.wf r)) = true at hwf
    change (if Nat.blt idx half then BinChunkTree.get? l idx
      else BinChunkTree.get? r (idx - half)) = some body at hGet
    have hRest : (BinChunkTree.wf l && BinChunkTree.wf r) = true := by
      cases h1 : Nat.beq (BinChunkTree.size l) half with
      | false =>
        rw [h1] at hwf
        nomatch hwf
      | true =>
        rw [h1] at hwf
        exact hwf
    have hWfL : BinChunkTree.wf l = true := by
      cases hw : BinChunkTree.wf l with
      | false =>
        rw [hw] at hRest
        nomatch hRest
      | true => rfl
    have hWfR : BinChunkTree.wf r = true := by
      rw [hWfL] at hRest
      exact hRest
    cases hBlt : Nat.blt idx half with
    | true =>
      rw [hBlt] at hGet
      exact ihL hWfL hLoc.1 hGet
    | false =>
      rw [hBlt] at hGet
      exact ihR hWfR hLoc.2 hGet

private theorem callsAdmitted_of_noCall (p : Program) (body : Body)
    (hNoCall : Trusted.MirSemantics.bodyHasAnyCall body = false) :
    Trusted.MirSemantics.callsAdmitted p body = true := by
  unfold Trusted.MirSemantics.callsAdmitted
  unfold Trusted.MirSemantics.bodyHasAnyCall at hNoCall
  have hAux : ∀ bbs : List BasicBlock,
      bbs.any (fun bb =>
        match bb.terminator with
        | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
        | _ => false) = false →
      bbs.all (fun bb =>
        match bb.terminator with
        | .call callee args dst target unwind =>
          match Trusted.MirSemantics.getElem? p.bodies callee with
          | none => false
          | some calleeBody =>
            !calleeBody.isUnsafe &&
              Trusted.MirSemantics.callTargetAdmitted body bb calleeBody args
                dst target unwind
        | .sysrootCall op args dst target unwind =>
          Trusted.MirSemantics.callTargetAdmitted body bb
            (Trusted.MirSemantics.sysrootNumBody op) args dst target unwind
        | _ => true) = true := by
    intro bbs
    induction bbs with
    | nil => intro _; rfl
    | cons bb rest ih =>
      intro hAny
      unfold List.any at hAny
      unfold List.all
      dsimp only at hAny
      dsimp only
      cases hTerm : bb.terminator with
      | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
        rw [hTerm] at hAny
        nomatch hAny
      | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
      | assert _ _ _ _ _ | coreCall _ _ _ _ _ | unsupported =>
        rw [hTerm] at hAny
        exact ih hAny
  exact hAux body.basicBlocks hNoCall

/-- Derive both `BodyStaticAdmitted p body = true` and
`bodyHasAnyCall body = false` from `BodyStaticIntrinsic body = true`. -/
theorem bodyStaticAdmitted_and_noCall_of_intrinsic {p : Program}
    {body : Body}
    (hPtr : Nat.beq p.pointerWidthBits 64 = true)
    (hProf : Nat.beq p.mirProfileVersion 1 = true)
    (hIntr : BodyStaticIntrinsic body = true) :
    BodyStaticAdmitted p body = true ∧
      Trusted.MirSemantics.bodyHasAnyCall body = false := by
  unfold BodyStaticIntrinsic at hIntr
  cases hNoCall : Trusted.MirSemantics.bodyHasAnyCall body with
  | true =>
    rw [hNoCall] at hIntr
    cases hPre : ((!Trusted.MirSemantics.stringIsEmpty body.identity) &&
      (!body.basicBlocks.isEmpty) &&
      Nat.blt body.argumentCount body.locals.length &&
      Trusted.MirSemantics.storageAnnotationsInBounds body &&
      Trusted.MirSemantics.discriminantTypesValid body &&
      Trusted.MirSemantics.castTypesValid body &&
      Trusted.MirSemantics.assertConditionTypesValid body &&
      body.locals.all Trusted.MirSemantics.isSupportedScalarOrUnitTy) with
    | true | false =>
      rw [hPre] at hIntr
      nomatch hIntr
  | false =>
    rw [hNoCall] at hIntr
    refine ⟨?_, rfl⟩
    unfold BodyStaticAdmitted Trusted.MirSemantics.singleBodyStaticAdmitted
      Trusted.MirSemantics.allCallBodiesStaticAdmitted
    rw [hPtr, hProf, hNoCall, callsAdmitted_of_noCall p body hNoCall]
    rw [Bool.not_false] at hIntr
    rw [Bool.true_and, Bool.true_and, hIntr]
    rfl

/-- Master compositional assembly theorem: lifts shard-local `TreeLocalVerified`
proofs (`Proof.Shard_000 .. Proof.Shard_{K-1}`) and `O(N log N)`
`ByteDecisionTree` uniqueness directly to `Trusted.MirSemantics.ProgramVerified`
on `p` (`p.bodies = BinChunkTree.toList t`). -/
theorem programVerified_of_shardedTree {p : Program} {specs : Specs}
    {t : BinChunkTree Body} (dt : ByteDecisionTree)
    (hBodies : p.bodies = BinChunkTree.toList t)
    (hPtr : Nat.beq p.pointerWidthBits 64 = true)
    (hProf : Nat.beq p.mirProfileVersion 1 = true)
    (hWf : BinChunkTree.wf t = true)
    (hEntry : Nat.blt p.entryDefId (BinChunkTree.size t) = true)
    (hPos : Nat.blt 0 (BinChunkTree.size t) = true)
    (hUniq : BinChunkTree.allIdx (checkBodyIdentityAt dt) t 0 = true)
    (hShards : TreeLocalVerified specs t)
    (hProp : specs.property p) :
    ProgramVerified p specs := by
  refine ⟨hPtr, hProf, ?_, ?_, ?_, ?_, hProp⟩
  · rw [hBodies]
    exact BinChunkTree.toList_nonEmpty_of_size_pos hPos
  · rw [hBodies, BinChunkTree.toList_length]
    exact hEntry
  · rw [hBodies]
    exact bodiesHaveUniqueIdentities_of_decisionTree dt hWf hUniq
  · intro defId body hFound
    rw [hBodies, BinChunkTree.getElem?_toList_eq_get? hWf defId] at hFound
    have hLoc := treeLocalVerified_get? hWf hShards hFound
    have ⟨hAdm, hNoCall⟩ :=
      bodyStaticAdmitted_and_noCall_of_intrinsic hPtr hProf hLoc.1
    have hFoundOrig : Trusted.MirSemantics.getElem? p.bodies defId =
        some body := by
      rw [hBodies, BinChunkTree.getElem?_toList_eq_get? hWf defId]
      exact hFound
    exact bodyVerified_of_safe hFoundOrig hAdm hLoc.2 hNoCall

/-- Lift a sharded `BinChunkTree` proof directly to
`Trusted.MirSemantics.CrateTheorem`. -/
theorem crateTheorem_of_shardedTree {c : Crate} {t : BinChunkTree Body}
    (dt : ByteDecisionTree)
    (hScope : c.program.scope = .crate)
    (hBodies : c.program.bodies = BinChunkTree.toList t)
    (hPtr : Nat.beq c.program.pointerWidthBits 64 = true)
    (hProf : Nat.beq c.program.mirProfileVersion 1 = true)
    (hWf : BinChunkTree.wf t = true)
    (hEntry : Nat.blt c.program.entryDefId (BinChunkTree.size t) = true)
    (hPos : Nat.blt 0 (BinChunkTree.size t) = true)
    (hUniq : BinChunkTree.allIdx (checkBodyIdentityAt dt) t 0 = true)
    (hShards : TreeLocalVerified c.specs t)
    (hProp : c.specs.property c.program) :
    CrateTheorem c :=
  ⟨hScope,
    programVerified_of_shardedTree dt hBodies hPtr hProf hWf hEntry hPos hUniq
      hShards hProp⟩

/-- Lift a sharded `BinChunkTree` proof directly to
`Trusted.MirSemantics.UnitTheorem`. -/
theorem unitTheorem_of_shardedTree {c : Crate} {t : BinChunkTree Body}
    (dt : ByteDecisionTree)
    (hScope : c.program.scope = .unit)
    (hBodies : c.program.bodies = BinChunkTree.toList t)
    (hPtr : Nat.beq c.program.pointerWidthBits 64 = true)
    (hProf : Nat.beq c.program.mirProfileVersion 1 = true)
    (hWf : BinChunkTree.wf t = true)
    (hEntry : Nat.blt c.program.entryDefId (BinChunkTree.size t) = true)
    (hPos : Nat.blt 0 (BinChunkTree.size t) = true)
    (hUniq : BinChunkTree.allIdx (checkBodyIdentityAt dt) t 0 = true)
    (hShards : TreeLocalVerified c.specs t)
    (hProp : c.specs.property c.program) :
    UnitTheorem c :=
  ⟨hScope,
    programVerified_of_shardedTree dt hBodies hPtr hProf hWf hEntry hPos hUniq
      hShards hProp⟩

end Anneal.SccSharding

end
