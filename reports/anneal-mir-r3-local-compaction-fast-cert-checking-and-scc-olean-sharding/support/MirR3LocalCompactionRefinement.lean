-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirSemantics

namespace AnnealMirR3Compaction

open Trusted.MirAst Trusted.MirSemantics

/-!
# MIR R3 Dead-Local Compaction, Fast O(S) Certificate Checking, and Bidirectional Equivalence

This module directly bridges MIR dead-local compaction (`R0 -> R3`: deleting
dead storage markers / `.nop` statements and injectively renumbering remaining
live locals `pi : LiveLocals -> Fin M` while preserving `_0` return place and
argument slots `_1.._argc`) onto unmodified `Trusted.MirAst` and
`Trusted.MirSemantics`.

Contents:
- **Part I**: Total list-reflection and `getElem?` / `setElem?` framing lemmas.
- **Part II**: `CompactionSpec`, `compactBody`, `compactProgram`, static side
  conditions (`PreservesAbiSlots`, `InjectiveOnLive`, `ValidTargetTypes`,
  `AllReferencedLocalsInLiveMask`, `StorageMarkersOnlyOnDead`), and boolean
  checkers (`checkBodyCompaction`, `checkProgramCompaction`).
- **Part III**: Block-suffix stuttering simulation, constructive
  `Classical.choice`-free `Diverges` preservation, `compact_preserves_eval_iff`,
  and fuel-bounded `wpProg_forward_of_compact` / `wpProg_transport_compact_iff`.
- **Part IV**: Side-by-side `O(S * L)` linear association-list checker
  (`checkR3LinearAssoc`) vs. `O(S)` positional active-frontier stride-8
  checker (`checkR3Positional`, `checkR3PositionalBatched`) with proved
  equational soundness (`checkR3PositionalBatched_eq`).
- **Part V**: Sharpness counterexamples (`CE1`, `CE2a`, `CE2b`, `CE2c`).
-/

/-! ## Part I: List Indexing, Reflection, and Framing Lemmas -/

private theorem bool_beq_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem nat_beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

private theorem nat_beq_refl (a : Nat) : Nat.beq a a = true :=
  Nat.beq_refl a

private theorem nat_blt_true_iff {a b : Nat} : Nat.blt a b = true ↔ a < b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

private theorem nat_ble_true_iff {a b : Nat} : Nat.ble a b = true ↔ a ≤ b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

private theorem nat_blt_false_iff {a b : Nat} : Nat.blt a b = false ↔ b ≤ a := by
  constructor
  · intro h
    cases Nat.lt_or_ge a b with
    | inl hlt =>
      have hblt : Nat.blt a b = true := Nat.ble_eq_true_of_le hlt
      rw [hblt] at h
      exact False.elim (Bool.noConfusion h)
    | inr hge => exact hge
  · intro h
    cases hlt : Nat.blt a b with
    | false => rfl
    | true =>
      have h1 : a < b := Nat.le_of_ble_eq_true hlt
      exact False.elim (Nat.not_lt_of_ge h h1)

private theorem nat_ble_false_iff {a b : Nat} : Nat.ble a b = false ↔ b < a :=
  nat_blt_false_iff (a := a) (b := b + 1)

private theorem intWidth_beq_eq {w1 w2 : IntWidth} (h : IntWidth.beq w1 w2 = true) :
    w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | cases h

private theorem mutability_beq_eq {m1 m2 : Mutability} (h : Mutability.beq m1 m2 = true) :
    m1 = m2 := by
  cases m1 <;> cases m2 <;> first | rfl | cases h

private theorem natListBeq_eq : ∀ {xs ys : List Nat}, natListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    change (Nat.beq x y && natListBeq xs ys) = true at h
    cases hx : Nat.beq x y with
    | false => rw [hx] at h; cases h
    | true =>
      rw [hx] at h
      rw [nat_beq_eq hx, natListBeq_eq h]

private theorem enumTy_beq_eq {e1 e2 : EnumTy} (h : EnumTy.beq e1 e2 = true) :
    e1 = e2 := by
  cases e1 with
  | mk id1 dw1 ds1 tr1 discs1 =>
    cases e2 with
    | mk id2 dw2 ds2 tr2 discs2 =>
      unfold EnumTy.beq at h
      dsimp only at h
      cases h1 : Nat.beq id1 id2 with
      | false => rw [h1] at h; cases h
      | true =>
        rw [h1] at h
        cases h2 : IntWidth.beq dw1 dw2 with
        | false => rw [h2] at h; cases h
        | true =>
          rw [h2] at h
          cases h3 : (ds1 == ds2) with
          | false => rw [h3] at h; cases h
          | true =>
            rw [h3] at h
            cases h4 : EnumTagRepr.beq tr1 tr2 with
            | false => rw [h4] at h; cases h
            | true =>
              rw [h4] at h
              have h4' : tr1 = tr2 := by
                cases tr1 with
                | zeroSized =>
                  cases tr2 with
                  | zeroSized => rfl
                  | scalar _ _ => cases h4
                | scalar wa sa =>
                  cases tr2 with
                  | zeroSized => cases h4
                  | scalar wb sb =>
                    change (IntWidth.beq wa wb && (sa == sb)) = true at h4
                    cases hwa : IntWidth.beq wa wb with
                    | false => rw [hwa] at h4; cases h4
                    | true =>
                      rw [hwa] at h4
                      rw [intWidth_beq_eq hwa, bool_beq_eq h4]
              rw [nat_beq_eq h1, intWidth_beq_eq h2, bool_beq_eq h3, h4', natListBeq_eq h]

mutual
  private theorem mirTy_beq_eq : ∀ {t1 t2 : MirTy}, MirTy.beq t1 t2 = true → t1 = t2
    | .bool, .bool, _ => rfl
    | .int w1 s1, .int w2 s2, h => by
      change (IntWidth.beq w1 w2 && (s1 == s2)) = true at h
      cases hw : IntWidth.beq w1 w2 with
      | false => rw [hw] at h; cases h
      | true =>
        rw [hw] at h
        rw [intWidth_beq_eq hw, bool_beq_eq h]
    | .unit, .unit, _ => rfl
    | .never, .never, _ => rfl
    | .enum e1, .enum e2, h => by
      change EnumTy.beq e1 e2 = true at h
      rw [enumTy_beq_eq h]
    | .tuple fs1, .tuple fs2, h => by
      change MirTy.beqList fs1 fs2 = true at h
      rw [mirTy_beqList_eq h]
    | .ref m1 p1, .ref m2 p2, h => by
      change (Mutability.beq m1 m2 && MirTy.beq p1 p2) = true at h
      cases hm : Mutability.beq m1 m2 with
      | false => rw [hm] at h; cases h
      | true =>
        rw [hm] at h
        rw [mutability_beq_eq hm, mirTy_beq_eq h]
    | .rawPtr m1 p1, .rawPtr m2 p2, h => by
      change (Mutability.beq m1 m2 && MirTy.beq p1 p2) = true at h
      cases hm : Mutability.beq m1 m2 with
      | false => rw [hm] at h; cases h
      | true =>
        rw [hm] at h
        rw [mutability_beq_eq hm, mirTy_beq_eq h]
    | .unsupported, .unsupported, _ => rfl
    | .bool, .int _ _, h | .bool, .unit, h | .bool, .never, h | .bool, .enum _, h
    | .bool, .tuple _, h | .bool, .ref _ _, h | .bool, .rawPtr _ _, h | .bool, .unsupported, h
    | .int _ _, .bool, h | .int _ _, .unit, h | .int _ _, .never, h | .int _ _, .enum _, h
    | .int _ _, .tuple _, h | .int _ _, .ref _ _, h | .int _ _, .rawPtr _ _, h | .int _ _, .unsupported, h
    | .unit, .bool, h | .unit, .int _ _, h | .unit, .never, h | .unit, .enum _, h
    | .unit, .tuple _, h | .unit, .ref _ _, h | .unit, .rawPtr _ _, h | .unit, .unsupported, h
    | .never, .bool, h | .never, .int _ _, h | .never, .unit, h | .never, .enum _, h
    | .never, .tuple _, h | .never, .ref _ _, h | .never, .rawPtr _ _, h | .never, .unsupported, h
    | .enum _, .bool, h | .enum _, .int _ _, h | .enum _, .unit, h | .enum _, .never, h
    | .enum _, .tuple _, h | .enum _, .ref _ _, h | .enum _, .rawPtr _ _, h | .enum _, .unsupported, h
    | .tuple _, .bool, h | .tuple _, .int _ _, h | .tuple _, .unit, h | .tuple _, .never, h
    | .tuple _, .enum _, h | .tuple _, .ref _ _, h | .tuple _, .rawPtr _ _, h | .tuple _, .unsupported, h
    | .ref _ _, .bool, h | .ref _ _, .int _ _, h | .ref _ _, .unit, h | .ref _ _, .never, h
    | .ref _ _, .enum _, h | .ref _ _, .tuple _, h | .ref _ _, .rawPtr _ _, h | .ref _ _, .unsupported, h
    | .rawPtr _ _, .bool, h | .rawPtr _ _, .int _ _, h | .rawPtr _ _, .unit, h | .rawPtr _ _, .never, h
    | .rawPtr _ _, .enum _, h | .rawPtr _ _, .tuple _, h | .rawPtr _ _, .ref _ _, h | .rawPtr _ _, .unsupported, h
    | .unsupported, .bool, h | .unsupported, .int _ _, h | .unsupported, .unit, h | .unsupported, .never, h
    | .unsupported, .enum _, h | .unsupported, .tuple _, h | .unsupported, .ref _ _, h | .unsupported, .rawPtr _ _, h => by
      cases h

  private theorem mirTy_beqList_eq : ∀ {fs1 fs2 : List MirTy}, MirTy.beqList fs1 fs2 = true → fs1 = fs2
    | [], [], _ => rfl
    | [], _ :: _, h => by cases h
    | _ :: _, [], h => by cases h
    | x :: xs, y :: ys, h => by
      change (MirTy.beq x y && MirTy.beqList xs ys) = true at h
      cases hx : MirTy.beq x y with
      | false => rw [hx] at h; cases h
      | true =>
        rw [hx] at h
        rw [mirTy_beq_eq hx, mirTy_beqList_eq h]
end

private theorem getElem?_eq_some_lt {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      Trusted.MirSemantics.getElem? xs i = some x → i < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, _ + 1, x, h => Nat.succ_lt_succ (getElem?_eq_some_lt (xs := xs) (x := x) h)

private theorem getElem?_lt_some {α : Type} :
    ∀ (xs : List α) {i : Nat}, i < xs.length →
      ∃ x, Trusted.MirSemantics.getElem? xs i = some x
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, _ + 1, h => getElem?_lt_some xs (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_none_iff {α : Type} :
    ∀ {xs : List α} {i : Nat},
      Trusted.MirSemantics.getElem? xs i = none ↔ xs.length ≤ i
  | [], i => ⟨fun _ => Nat.zero_le i, fun _ => rfl⟩
  | _ :: _, 0 => by
    constructor
    · intro h; cases h
    · intro h; exact False.elim (Nat.not_succ_le_zero _ h)
  | _ :: xs, n + 1 => by
    have ih := getElem?_none_iff (xs := xs) (i := n)
    constructor
    · intro h
      exact Nat.succ_le_succ (ih.mp h)
    · intro h
      exact ih.mpr (Nat.le_of_succ_le_succ h)

private theorem setElem?_lt_some {α : Type} :
    ∀ (xs : List α) {i : Nat} (v : α), i < xs.length →
      ∃ xs', setElem? xs i v = some xs' ∧ xs'.length = xs.length
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: xs, 0, v, _ => ⟨v :: xs, rfl, rfl⟩
  | x :: xs, n + 1, v, h => by
    let ⟨xs', hSet, hLen⟩ := setElem?_lt_some xs v (Nat.lt_of_succ_lt_succ h)
    refine ⟨x :: xs', ?_, ?_⟩
    · change (match setElem? xs n v with | some xs'' => some (x :: xs'') | none => none) = some (x :: xs')
      rw [hSet]
    · exact congrArg Nat.succ hLen

private theorem setElem?_some_length {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      setElem? xs i v = some xs' → xs'.length = xs.length
  | [], _, _, _, h => by cases h
  | _ :: xs, _, 0, v, h => by
    injection h with hEq
    subst hEq
    rfl
  | x :: xs, xs', n + 1, v, h => by
    change (match setElem? xs n v with | some xs'' => some (x :: xs'') | none => none) = some xs' at h
    cases hSub : setElem? xs n v with
    | none => rw [hSub] at h; cases h
    | some ys =>
      rw [hSub] at h
      injection h with hEq
      subst hEq
      exact congrArg Nat.succ (setElem?_some_length hSub)

private theorem getElem?_setElem?_same {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      setElem? xs i v = some xs' →
      Trusted.MirSemantics.getElem? xs' i = some v
  | [], _, _, _, h => by cases h
  | _ :: xs, _, 0, v, h => by
    injection h with hEq
    subst hEq
    rfl
  | x :: xs, xs', n + 1, v, h => by
    change (match setElem? xs n v with | some xs'' => some (x :: xs'') | none => none) = some xs' at h
    cases hSub : setElem? xs n v with
    | none => rw [hSub] at h; cases h
    | some ys =>
      rw [hSub] at h
      injection h with hEq
      subst hEq
      change Trusted.MirSemantics.getElem? ys n = some v
      exact getElem?_setElem?_same hSub

private theorem getElem?_setElem?_ne {α : Type} :
    ∀ {xs xs' : List α} {i j : Nat} {v : α},
      i ≠ j → setElem? xs i v = some xs' →
      Trusted.MirSemantics.getElem? xs' j = Trusted.MirSemantics.getElem? xs j
  | [], _, _, _, _, _, h => by cases h
  | _ :: xs, _, 0, 0, _, hNe, _ => False.elim (hNe rfl)
  | _ :: xs, _, 0, j + 1, v, _, h => by
    injection h with hEq
    subst hEq
    rfl
  | x :: xs, xs', i + 1, 0, v, _, h => by
    change (match setElem? xs i v with | some xs'' => some (x :: xs'') | none => none) = some xs' at h
    cases hSub : setElem? xs i v with
    | none => rw [hSub] at h; cases h
    | some ys =>
      rw [hSub] at h
      injection h with hEq
      subst hEq
      rfl
  | x :: xs, xs', i + 1, j + 1, v, hNe, h => by
    change (match setElem? xs i v with | some xs'' => some (x :: xs'') | none => none) = some xs' at h
    cases hSub : setElem? xs i v with
    | none => rw [hSub] at h; cases h
    | some ys =>
      rw [hSub] at h
      injection h with hEq
      subst hEq
      change Trusted.MirSemantics.getElem? ys j = Trusted.MirSemantics.getElem? xs j
      exact getElem?_setElem?_ne (fun hEq => hNe (congrArg Nat.succ hEq)) hSub

private theorem list_all_getElem? {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, xs.all p = true →
      ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = true
  | [], _, _, _, h => by cases h
  | x :: xs, hAll, 0, y, hGet => by
    injection hGet with hEq
    subst hEq
    change (p x && xs.all p) = true at hAll
    cases hpx : p x with
    | false => rw [hpx] at hAll; cases hAll
    | true => rfl
  | x :: xs, hAll, n + 1, y, hGet => by
    change (p x && xs.all p) = true at hAll
    cases hpx : p x with
    | false => rw [hpx] at hAll; cases hAll
    | true =>
      rw [hpx] at hAll
      exact list_all_getElem? p hAll n y hGet

private theorem list_all_of_getElem? {α : Type} (p : α → Bool) :
    ∀ {xs : List α},
      (∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = true) →
      xs.all p = true
  | [], _ => rfl
  | x :: xs, h => by
    change (p x && xs.all p) = true
    have h0 : p x = true := h 0 x rfl
    have hRest : xs.all p = true :=
      list_all_of_getElem? p (fun i y hy => h (i + 1) y hy)
    rw [h0, hRest]
    rfl

private theorem list_any_false_of_getElem? {α : Type} (p : α → Bool) :
    ∀ {xs : List α},
      (∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = false) →
      xs.any p = false
  | [], _ => rfl
  | x :: xs, h => by
    change (p x || xs.any p) = false
    have h0 : p x = false := h 0 x rfl
    have hRest : xs.any p = false :=
      list_any_false_of_getElem? p (fun i y hy => h (i + 1) y hy)
    rw [h0, hRest]
    rfl

private theorem list_any_false_elim {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, xs.any p = false →
      ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = false
  | [], _, _, _, h => by cases h
  | x :: xs, hAny, 0, y, hGet => by
    injection hGet with hEq
    subst hEq
    change (p x || xs.any p) = false at hAny
    cases hpx : p x with
    | true => rw [hpx] at hAny; cases hAny
    | false => rfl
  | x :: xs, hAny, n + 1, y, hGet => by
    change (p x || xs.any p) = false at hAny
    cases hpx : p x with
    | true => rw [hpx] at hAny; cases hAny
    | false =>
      rw [hpx] at hAny
      exact list_any_false_elim p hAny n y hGet

private theorem drop_getElem?_succ {α : Type} :
    ∀ (xs : List α) (i : Nat) (x : α),
      Trusted.MirSemantics.getElem? xs i = some x →
      xs.drop i = x :: xs.drop (i + 1)
  | [], _, _, h => by cases h
  | x :: _, 0, y, h => by
    injection h with hEq
    subst hEq
    rfl
  | _ :: xs, n + 1, y, h => drop_getElem?_succ xs n y h

private theorem drop_length_eq_nil {α : Type} :
    ∀ (xs : List α), xs.drop xs.length = []
  | [] => rfl
  | _ :: xs => drop_length_eq_nil xs

private theorem drop_eq_nil_iff {α : Type} :
    ∀ (xs : List α) (i : Nat), i ≤ xs.length → (xs.drop i = [] ↔ i = xs.length)
  | [], 0, _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], i + 1, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: _, 0, _ => by
    constructor <;> intro h <;> cases h
  | _ :: xs, i + 1, h => by
    have ih := drop_eq_nil_iff xs i (Nat.le_of_succ_le_succ h)
    constructor
    · intro hDrop
      exact congrArg Nat.succ (ih.mp hDrop)
    · intro hEq
      exact ih.mpr (Nat.succ.inj hEq)

private theorem drop_eq_cons_getElem? {α : Type} :
    ∀ {xs : List α} {i : Nat} {y : α} {ys : List α},
      xs.drop i = y :: ys →
      Trusted.MirSemantics.getElem? xs i = some y ∧ xs.drop (i + 1) = ys
  | [], 0, _, _, h => by cases h
  | [], _ + 1, _, _, h => by cases h
  | x :: xs, 0, y, ys, h => by
    injection h with h1 h2
    subst h1; subst h2
    exact ⟨rfl, rfl⟩
  | _ :: xs, i + 1, y, ys, h => drop_eq_cons_getElem? (xs := xs) (i := i) h

private theorem list_take_eq_of_getElem? {α : Type} :
    ∀ (n : Nat) (xs ys : List α),
      n ≤ xs.length →
      n ≤ ys.length →
      (∀ i, i < n → Trusted.MirSemantics.getElem? xs i = Trusted.MirSemantics.getElem? ys i) →
      xs.take n = ys.take n
  | 0, _, _, _, _, _ => rfl
  | n + 1, [], _, hxs, _, _ => False.elim (Nat.not_succ_le_zero _ hxs)
  | n + 1, _ :: _, [], _, hys, _ => False.elim (Nat.not_succ_le_zero _ hys)
  | n + 1, x :: xs, y :: ys, hxs, hys, hGet => by
    have h0 : Trusted.MirSemantics.getElem? (x :: xs) 0 =
        Trusted.MirSemantics.getElem? (y :: ys) 0 :=
      hGet 0 (Nat.zero_lt_succ n)
    injection h0 with hxy
    subst hxy
    have hTail : xs.take n = ys.take n :=
      list_take_eq_of_getElem? n xs ys
        (Nat.le_of_succ_le_succ hxs)
        (Nat.le_of_succ_le_succ hys)
        (fun i hi => hGet (i + 1) (Nat.succ_lt_succ hi))
    change x :: xs.take n = x :: ys.take n
    rw [hTail]

/-! ## Part II: Dead-Local Identification and Injective Slot Compaction -/

/-- Compaction specification for a single MIR function body:
- `liveMask`: boolean mask over source locals `0 .. bSrc.locals.length - 1`
  (`true` = preserved live local; `false` = dead local to compact away).
- `slotMap`: slot-renumbering table `pi` mapping each live source local
  `i` to its compacted target index `pi i < targetLocals.length`.
- `targetLocals`: compacted `MirTy` list of length `M = targetLocals.length`. -/
structure CompactionSpec where
  liveMask : List Bool
  slotMap : List Nat
  targetLocals : List MirTy

/-- Check whether source local `i` is marked live in `mask`. -/
noncomputable def isLiveLocal (mask : List Bool) (i : LocalId) : Bool :=
  match Trusted.MirSemantics.getElem? mask i with
  | some b => b
  | none => false

/-- Look up the compacted target local index `pi(i)` in `smap`. -/
noncomputable def mapLocal (smap : List Nat) (i : LocalId) : LocalId :=
  match Trusted.MirSemantics.getElem? smap i with
  | some k => k
  | none => 0

/-- Explicit dependent renumbering map `pi : LiveLocals -> Fin M`
witnessing that every live local maps into `Fin spec.targetLocals.length`. -/
noncomputable def piFin (spec : CompactionSpec)
    (hBound : ∀ i : LocalId, isLiveLocal spec.liveMask i = true →
      mapLocal spec.slotMap i < spec.targetLocals.length)
    (i : LocalId) (hi : isLiveLocal spec.liveMask i = true) :
    Fin spec.targetLocals.length :=
  ⟨mapLocal spec.slotMap i, hBound i hi⟩

/-- Remap a `Place`'s base `localId` via `smap`. -/
noncomputable def remapPlace (smap : List Nat) (p : Place) : Place :=
  { p with localId := mapLocal smap p.localId }

/-- Remap local references inside an `Operand`. -/
noncomputable def remapOperand (smap : List Nat) : Operand → Operand
  | .copy p => .copy (remapPlace smap p)
  | .move p => .move (remapPlace smap p)
  | .constant c => .constant c

/-- Elementwise remapping over `List Operand`. -/
noncomputable def remapOperandList (smap : List Nat) : List Operand → List Operand
  | [] => []
  | op :: ops => remapOperand smap op :: remapOperandList smap ops

/-- Remap local references inside an `Rvalue`. -/
noncomputable def remapRvalue (smap : List Nat) : Rvalue → Rvalue
  | .use op => .use (remapOperand smap op)
  | .binaryOp op l r => .binaryOp op (remapOperand smap l) (remapOperand smap r)
  | .unaryOp op x => .unaryOp op (remapOperand smap x)
  | .discriminant p => .discriminant (remapPlace smap p)
  | .ref m p => .ref m (remapPlace smap p)
  | .addressOf m p => .addressOf m (remapPlace smap p)
  | .aggregateTuple fs => .aggregateTuple (remapOperandList smap fs)
  | .unsupported => .unsupported

/-- Delete `.nop`, `.storageLive`, and `.storageDead` statements while remapping
surviving `.assign` statements (`R0 -> R3`). -/
noncomputable def compactStatements (smap : List Nat) :
    List StatementKind → List StatementKind
  | [] => []
  | .nop :: rest => compactStatements smap rest
  | .storageLive _ :: rest => compactStatements smap rest
  | .storageDead _ :: rest => compactStatements smap rest
  | .assign dst rv :: rest =>
    .assign (remapPlace smap dst) (remapRvalue smap rv) ::
      compactStatements smap rest
  | .unsupported :: rest => .unsupported :: compactStatements smap rest

/-- Remap local references inside a `TerminatorKind`. -/
noncomputable def remapTerminator (smap : List Nat) : TerminatorKind → TerminatorKind
  | .goto tgt => .goto tgt
  | .switchInt discr tgts => .switchInt (remapOperand smap discr) tgts
  | .return_ => .return_
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert cond exp msg tgt uw =>
    .assert (remapOperand smap cond) exp msg tgt uw
  | .call callee args dst tgt uw =>
    .call callee (remapOperandList smap args) (remapPlace smap dst) tgt uw
  | .unsupported => .unsupported

/-- Compact a single `BasicBlock`. -/
noncomputable def compactBasicBlock (smap : List Nat) (bb : BasicBlock) : BasicBlock :=
  { bb with
    statements := compactStatements smap bb.statements
    terminator := remapTerminator smap bb.terminator }

/-- Elementwise compaction over `List BasicBlock`. -/
noncomputable def compactBasicBlockList (smap : List Nat) :
    List BasicBlock → List BasicBlock
  | [] => []
  | bb :: bbs => compactBasicBlock smap bb :: compactBasicBlockList smap bbs

/-- Compact a `Body` using `spec` (`R0 -> R3`), replacing `locals` with
`spec.targetLocals`, deleting dead storage markers / `.nop`s, and remapping all
remaining local indices via `spec.slotMap`. -/
noncomputable def compactBody (spec : CompactionSpec) (b : Body) : Body :=
  { b with
    locals := spec.targetLocals
    basicBlocks := compactBasicBlockList spec.slotMap b.basicBlocks }

/-- Compact every body in `bodies` pairwise with `specs`. -/
noncomputable def compactBodyList :
    List CompactionSpec → List Body → List Body
  | [], _ => []
  | _, [] => []
  | sp :: sps, b :: bs => compactBody sp b :: compactBodyList sps bs

/-- Compact all bodies in `p` according to `specs`, preserving `entryDefId`,
`pointerWidthBits`, `mirProfileVersion`, and `scope`. -/
noncomputable def compactProgram (specs : List CompactionSpec) (p : Program) :
    Program :=
  { p with bodies := compactBodyList specs p.bodies }

/-! ### Static Compaction Well-Formedness Predicates & Checkers -/

/-- Return slot `_0` and argument slots `_1.._argc` remain live and map to
themselves (`pi i = i`). -/
def PreservesAbiSlots (argc : Nat) (spec : CompactionSpec) : Prop :=
  argc < spec.liveMask.length ∧
  ∀ i : LocalId, i ≤ argc →
    isLiveLocal spec.liveMask i = true ∧ mapLocal spec.slotMap i = i

/-- `pi` is injective on all live source locals (`isLiveLocal = true`). -/
def InjectiveOnLive (spec : CompactionSpec) : Prop :=
  ∀ i j : LocalId,
    isLiveLocal spec.liveMask i = true →
    isLiveLocal spec.liveMask j = true →
    mapLocal spec.slotMap i = mapLocal spec.slotMap j →
    i = j

/-- Target locals cover every live source local with matching `MirTy` and valid
`isSupportedScalarOrUnitTy` status, while dead source locals also satisfy
`isSupportedScalarOrUnitTy`. -/
def ValidTargetTypes (bSrc : Body) (spec : CompactionSpec) : Prop :=
  spec.liveMask.length = bSrc.locals.length ∧
  bSrc.argumentCount < spec.targetLocals.length ∧
  spec.targetLocals.all isSupportedScalarOrUnitTy = true ∧
  bSrc.locals.all isSupportedScalarOrUnitTy = true ∧
  ∀ i : LocalId, isLiveLocal spec.liveMask i = true →
    mapLocal spec.slotMap i < spec.targetLocals.length ∧
    Trusted.MirSemantics.getElem? spec.targetLocals (mapLocal spec.slotMap i) =
      Trusted.MirSemantics.getElem? bSrc.locals i

/-- Check whether every local referenced by `Operand` is live in `mask`. -/
noncomputable def operandLocalsInMask (mask : List Bool) : Operand → Bool
  | .copy p | .move p => isLiveLocal mask p.localId
  | .constant _ => true

/-- Check whether every local in `List Operand` is live in `mask`. -/
noncomputable def operandListLocalsInMask (mask : List Bool) : List Operand → Bool
  | [] => true
  | op :: ops => operandLocalsInMask mask op && operandListLocalsInMask mask ops

/-- Check whether every local referenced by `Rvalue` is live in `mask`. -/
noncomputable def rvalueLocalsInMask (mask : List Bool) : Rvalue → Bool
  | .use op => operandLocalsInMask mask op
  | .binaryOp _ l r => operandLocalsInMask mask l && operandLocalsInMask mask r
  | .unaryOp _ x => operandLocalsInMask mask x
  | .discriminant p | .ref _ p | .addressOf _ p => isLiveLocal mask p.localId
  | .aggregateTuple fs => operandListLocalsInMask mask fs
  | .unsupported => true

/-- Check whether every non-marker local reference in `StatementKind` is live
in `mask`. -/
noncomputable def stmtRefLocalsInMask (mask : List Bool) : StatementKind → Bool
  | .assign dst rv => isLiveLocal mask dst.localId && rvalueLocalsInMask mask rv
  | .storageLive _ | .storageDead _ | .nop | .unsupported => true

/-- Check whether every local reference in `TerminatorKind` is live in `mask`. -/
noncomputable def termLocalsInMask (mask : List Bool) : TerminatorKind → Bool
  | .switchInt discr _ => operandLocalsInMask mask discr
  | .assert cond _ _ _ _ => operandLocalsInMask mask cond
  | .call _ args dst _ _ => operandListLocalsInMask mask args && isLiveLocal mask dst.localId
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true

/-- Check whether every referenced local across all blocks of `bSrc` is in `mask`. -/
noncomputable def allReferencedLocalsInLiveMaskBool (mask : List Bool) (bSrc : Body) :
    Bool :=
  bSrc.basicBlocks.all (fun bb =>
    bb.statements.all (stmtRefLocalsInMask mask) &&
    termLocalsInMask mask bb.terminator)

/-- Propositional statement that all referenced locals in `bSrc` belong to `mask`. -/
def AllReferencedLocalsInLiveMask (mask : List Bool) (bSrc : Body) : Prop :=
  allReferencedLocalsInLiveMaskBool mask bSrc = true

/-- Check whether every `.storageLive` / `.storageDead` in `stmt` targets strictly
an in-bounds dead local (`id < numLocals`, `0 < id` for `.storageDead`, and
`isLiveLocal mask id = false`). -/
noncomputable def stmtStorageOnlyOnDead (mask : List Bool) (numLocals : Nat) :
    StatementKind → Bool
  | .storageLive id => Nat.blt id numLocals && !(isLiveLocal mask id)
  | .storageDead id => !Nat.beq id 0 && Nat.blt id numLocals && !(isLiveLocal mask id)
  | .assign _ _ | .nop | .unsupported => true

/-- Check that every `.storageLive`/`.storageDead` annotation in `bSrc` lies in
bounds and targets only dead locals (`!isLiveLocal`). -/
noncomputable def storageMarkersOnlyOnDeadBool (mask : List Bool) (numLocals : Nat)
    (bSrc : Body) : Bool :=
  bSrc.basicBlocks.all (fun bb =>
    bb.statements.all (stmtStorageOnlyOnDead mask numLocals))

/-- Propositional statement that storage markers in `bSrc` target only in-bounds
dead locals (`id ≠ 0` for `.storageDead`). -/
def StorageMarkersOnlyOnDead (mask : List Bool) (numLocals : Nat) (bSrc : Body) :
    Prop :=
  storageMarkersOnlyOnDeadBool mask numLocals bSrc = true

/-- Complete per-body validity contract for `R0 -> R3` compaction. -/
def ValidBodyCompaction (bSrc : Body) (spec : CompactionSpec) : Prop :=
  PreservesAbiSlots bSrc.argumentCount spec ∧
  InjectiveOnLive spec ∧
  ValidTargetTypes bSrc spec ∧
  AllReferencedLocalsInLiveMask spec.liveMask bSrc ∧
  StorageMarkersOnlyOnDead spec.liveMask bSrc.locals.length bSrc

/-- Whole-program compaction contract: `specs` matches `pSrc.bodies` elementwise. -/
def ValidProgramCompaction (specs : List CompactionSpec) (pSrc : Program) : Prop :=
  specs.length = pSrc.bodies.length ∧
  ∀ (defId : DefId) (bSrc : Body) (spec : CompactionSpec),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? specs defId = some spec →
    ValidBodyCompaction bSrc spec

/-- Executable boolean checks corresponding to `PreservesAbiSlots`,
`InjectiveOnLive`, and `ValidTargetTypes`. -/
noncomputable def checkAbiLoop (argc : Nat) (spec : CompactionSpec) : Nat → Bool
  | 0 => isLiveLocal spec.liveMask 0 && Nat.beq (mapLocal spec.slotMap 0) 0
  | n + 1 =>
    isLiveLocal spec.liveMask (n + 1) &&
      Nat.beq (mapLocal spec.slotMap (n + 1)) (n + 1) &&
      checkAbiLoop argc spec n

noncomputable def checkInjectiveAgainst (spec : CompactionSpec) (i : Nat) : Nat → Bool
  | 0 => true
  | j + 1 =>
    let okPair :=
      if Nat.beq i j then true
      else if isLiveLocal spec.liveMask i && isLiveLocal spec.liveMask j then
        !Nat.beq (mapLocal spec.slotMap i) (mapLocal spec.slotMap j)
      else true
    okPair && checkInjectiveAgainst spec i j

noncomputable def checkInjectiveLoop (spec : CompactionSpec) (total : Nat) : Nat → Bool
  | 0 => true
  | i + 1 => checkInjectiveAgainst spec i total && checkInjectiveLoop spec total i

noncomputable def checkTargetTypesLoop (bSrc : Body) (spec : CompactionSpec) : Nat → Bool
  | 0 => true
  | i + 1 =>
    let okI :=
      if isLiveLocal spec.liveMask i then
        match Trusted.MirSemantics.getElem? spec.targetLocals (mapLocal spec.slotMap i),
            Trusted.MirSemantics.getElem? bSrc.locals i with
        | some tTgt, some tSrc => MirTy.beq tTgt tSrc
        | _, _ => false
      else true
    okI && checkTargetTypesLoop bSrc spec i

/-- Total executable boolean validator for `ValidBodyCompaction`. -/
noncomputable def checkBodyCompaction (bSrc : Body) (spec : CompactionSpec) : Bool :=
  Nat.beq spec.liveMask.length bSrc.locals.length &&
    Nat.blt bSrc.argumentCount spec.liveMask.length &&
    Nat.blt bSrc.argumentCount spec.targetLocals.length &&
    spec.targetLocals.all isSupportedScalarOrUnitTy &&
    bSrc.locals.all isSupportedScalarOrUnitTy &&
    checkAbiLoop bSrc.argumentCount spec bSrc.argumentCount &&
    checkInjectiveLoop spec spec.liveMask.length spec.liveMask.length &&
    checkTargetTypesLoop bSrc spec spec.liveMask.length &&
    allReferencedLocalsInLiveMaskBool spec.liveMask bSrc &&
    storageMarkersOnlyOnDeadBool spec.liveMask bSrc.locals.length bSrc

/-- Total executable boolean validator for `ValidProgramCompaction`. -/
noncomputable def checkProgramCompactionList :
    List CompactionSpec → List Body → Bool
  | [], [] => true
  | sp :: sps, b :: bs => checkBodyCompaction b sp && checkProgramCompactionList sps bs
  | _, _ => false

noncomputable def checkProgramCompaction (specs : List CompactionSpec) (pSrc : Program) :
    Bool :=
  checkProgramCompactionList specs pSrc.bodies


/-! ## Part III: Soundness of Compaction Checkers and Bidirectional Equivalence (`compact_preserves_eval_iff`) -/

private theorem isLiveLocal_eq_true_iff {mask : List Bool} {i : Nat} :
    isLiveLocal mask i = true ↔ Trusted.MirSemantics.getElem? mask i = some true := by
  unfold isLiveLocal
  cases h : Trusted.MirSemantics.getElem? mask i with
  | none => constructor <;> intro h1 <;> cases h1
  | some b =>
    cases b with
    | false => constructor <;> intro h1 <;> cases h1
    | true => exact ⟨fun _ => rfl, fun _ => rfl⟩

private theorem isLiveLocal_eq_true_lt {mask : List Bool} {i : Nat}
    (h : isLiveLocal mask i = true) : i < mask.length :=
  getElem?_eq_some_lt (isLiveLocal_eq_true_iff.mp h)

private theorem isLiveLocal_eq_false_of_ge {mask : List Bool} {i : Nat}
    (h : mask.length ≤ i) : isLiveLocal mask i = false := by
  unfold isLiveLocal
  rw [getElem?_none_iff.mpr h]

private theorem bool_ite_pos {α : Type} {c : Bool} {d : Decidable (c = true)}
    (hc : c = true) (a b : α) :
    @ite α (c = true) d a b = a := by
  cases d with
  | isTrue _ => rfl
  | isFalse hne => exact False.elim (hne hc)

private theorem bool_ite_neg {α : Type} {c : Bool} {d : Decidable (c = true)}
    (hc : c = false) (a b : α) :
    @ite α (c = true) d a b = b := by
  cases d with
  | isTrue ht => rw [hc] at ht; cases ht
  | isFalse _ => rfl

private theorem checkAbiLoop_sound {argc : Nat} {spec : CompactionSpec} :
    ∀ (n : Nat), checkAbiLoop argc spec n = true →
      ∀ i : LocalId, i ≤ n →
        isLiveLocal spec.liveMask i = true ∧ mapLocal spec.slotMap i = i
  | 0, h, i, hi => by
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    change (isLiveLocal spec.liveMask 0 && Nat.beq (mapLocal spec.slotMap 0) 0) = true at h
    cases h1 : isLiveLocal spec.liveMask 0 with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      exact ⟨rfl, nat_beq_eq h⟩
  | n + 1, h, i, hi => by
    change (isLiveLocal spec.liveMask (n + 1) &&
      Nat.beq (mapLocal spec.slotMap (n + 1)) (n + 1) &&
      checkAbiLoop argc spec n) = true at h
    cases h1 : isLiveLocal spec.liveMask (n + 1) with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      cases h2 : Nat.beq (mapLocal spec.slotMap (n + 1)) (n + 1) with
      | false => rw [h2] at h; cases h
      | true =>
        rw [h2] at h
        cases Nat.eq_or_lt_of_le hi with
        | inl hEq =>
          subst hEq
          exact ⟨h1, nat_beq_eq h2⟩
        | inr hLt =>
          exact checkAbiLoop_sound n h i (Nat.le_of_lt_succ hLt)

private theorem checkInjectiveAgainst_sound {spec : CompactionSpec} (i : Nat) :
    ∀ (n : Nat), checkInjectiveAgainst spec i n = true →
      ∀ j : Nat, j < n →
        isLiveLocal spec.liveMask i = true →
        isLiveLocal spec.liveMask j = true →
        mapLocal spec.slotMap i = mapLocal spec.slotMap j →
        i = j
  | 0, _, _, hj, _, _, _ => False.elim (Nat.not_lt_zero _ hj)
  | n + 1, h, j, hj, hiLive, hjLive, hMap => by
    unfold checkInjectiveAgainst at h
    dsimp only at h
    cases h1 : (if Nat.beq i n then true
        else if isLiveLocal spec.liveMask i && isLiveLocal spec.liveMask n then
          !Nat.beq (mapLocal spec.slotMap i) (mapLocal spec.slotMap n)
        else true) with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with
      | inr hjLt =>
        exact checkInjectiveAgainst_sound i n h j hjLt hiLive hjLive hMap
      | inl hjEq =>
        subst hjEq
        cases hij : Nat.beq i j with
        | true => exact nat_beq_eq hij
        | false =>
          rw [bool_ite_neg hij] at h1
          have hBoth : (isLiveLocal spec.liveMask i && isLiveLocal spec.liveMask j) = true := by
            rw [hiLive, hjLive]
            rfl
          rw [bool_ite_pos hBoth] at h1
          rw [hMap, nat_beq_refl] at h1
          cases h1

private theorem checkInjectiveLoop_sound {spec : CompactionSpec} (total : Nat) :
    ∀ (m : Nat), checkInjectiveLoop spec total m = true →
      ∀ i j : Nat, i < m → j < total →
        isLiveLocal spec.liveMask i = true →
        isLiveLocal spec.liveMask j = true →
        mapLocal spec.slotMap i = mapLocal spec.slotMap j →
        i = j
  | 0, _, _, _, hi, _, _, _, _ => False.elim (Nat.not_lt_zero _ hi)
  | m + 1, h, i, j, hi, hj, hiLive, hjLive, hMap => by
    change (checkInjectiveAgainst spec m total &&
      checkInjectiveLoop spec total m) = true at h
    cases h1 : checkInjectiveAgainst spec m total with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
      | inl hiEq =>
        subst hiEq
        exact checkInjectiveAgainst_sound i total h1 j hj hiLive hjLive hMap
      | inr hiLt =>
        exact checkInjectiveLoop_sound total m h i j hiLt hj hiLive hjLive hMap

private theorem checkTargetTypesLoop_sound {bSrc : Body} {spec : CompactionSpec} :
    ∀ (m : Nat), checkTargetTypesLoop bSrc spec m = true →
      ∀ i : Nat, i < m →
        isLiveLocal spec.liveMask i = true →
        mapLocal spec.slotMap i < spec.targetLocals.length ∧
        Trusted.MirSemantics.getElem? spec.targetLocals (mapLocal spec.slotMap i) =
          Trusted.MirSemantics.getElem? bSrc.locals i
  | 0, _, _, hi, _ => False.elim (Nat.not_lt_zero _ hi)
  | m + 1, h, i, hi, hiLive => by
    unfold checkTargetTypesLoop at h
    dsimp only at h
    cases h1 : (if isLiveLocal spec.liveMask m then
        match Trusted.MirSemantics.getElem? spec.targetLocals (mapLocal spec.slotMap m),
            Trusted.MirSemantics.getElem? bSrc.locals m with
        | some tTgt, some tSrc => MirTy.beq tTgt tSrc
        | _, _ => false
      else true) with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
      | inr hiLt =>
        exact checkTargetTypesLoop_sound m h i hiLt hiLive
      | inl hiEq =>
        subst hiEq
        rw [bool_ite_pos hiLive] at h1
        cases hTgt : Trusted.MirSemantics.getElem? spec.targetLocals (mapLocal spec.slotMap i) with
        | none => rw [hTgt] at h1; cases h1
        | some tTgt =>
          rw [hTgt] at h1
          cases hSrc : Trusted.MirSemantics.getElem? bSrc.locals i with
          | none => rw [hSrc] at h1; cases h1
          | some tSrc =>
            rw [hSrc] at h1
            have hEqTy := mirTy_beq_eq h1
            subst hEqTy
            exact ⟨getElem?_eq_some_lt hTgt, rfl⟩

/-- Soundness of the executable boolean validator `checkBodyCompaction`. -/
theorem validBodyCompaction_of_check {bSrc : Body} {spec : CompactionSpec}
    (h : checkBodyCompaction bSrc spec = true) :
    ValidBodyCompaction bSrc spec := by
  unfold checkBodyCompaction at h
  cases hLen : Nat.beq spec.liveMask.length bSrc.locals.length with
  | false => rw [hLen] at h; cases h
  | true =>
    rw [hLen] at h
    cases hArgMask : Nat.blt bSrc.argumentCount spec.liveMask.length with
    | false => rw [hArgMask] at h; cases h
    | true =>
      rw [hArgMask] at h
      cases hArgTgt : Nat.blt bSrc.argumentCount spec.targetLocals.length with
      | false => rw [hArgTgt] at h; cases h
      | true =>
        rw [hArgTgt] at h
        cases hTgtAll : spec.targetLocals.all isSupportedScalarOrUnitTy with
        | false => rw [hTgtAll] at h; cases h
        | true =>
          rw [hTgtAll] at h
          cases hSrcAll : bSrc.locals.all isSupportedScalarOrUnitTy with
          | false => rw [hSrcAll] at h; cases h
          | true =>
            rw [hSrcAll] at h
            cases hAbi : checkAbiLoop bSrc.argumentCount spec bSrc.argumentCount with
            | false => rw [hAbi] at h; cases h
            | true =>
              rw [hAbi] at h
              cases hInj : checkInjectiveLoop spec spec.liveMask.length spec.liveMask.length with
              | false => rw [hInj] at h; cases h
              | true =>
                rw [hInj] at h
                cases hTy : checkTargetTypesLoop bSrc spec spec.liveMask.length with
                | false => rw [hTy] at h; cases h
                | true =>
                  rw [hTy] at h
                  cases hRef : allReferencedLocalsInLiveMaskBool spec.liveMask bSrc with
                  | false => rw [hRef] at h; cases h
                  | true =>
                    rw [hRef] at h
                    refine ⟨⟨nat_blt_true_iff.mp hArgMask, checkAbiLoop_sound bSrc.argumentCount hAbi⟩,
                      ?_, ?_, hRef, h⟩
                    · intro i j hi hj hMap
                      exact checkInjectiveLoop_sound spec.liveMask.length spec.liveMask.length hInj
                        i j (isLiveLocal_eq_true_lt hi) (isLiveLocal_eq_true_lt hj) hi hj hMap
                    · refine ⟨nat_beq_eq hLen, nat_blt_true_iff.mp hArgTgt, hTgtAll, hSrcAll, ?_⟩
                      intro i hi
                      exact checkTargetTypesLoop_sound spec.liveMask.length hTy i
                        (isLiveLocal_eq_true_lt hi) hi

private theorem checkProgramCompactionList_length :
    ∀ {sps : List CompactionSpec} {bs : List Body},
      checkProgramCompactionList sps bs = true → sps.length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | sp :: sps, b :: bs, h => by
    change (checkBodyCompaction b sp && checkProgramCompactionList sps bs) = true at h
    cases h1 : checkBodyCompaction b sp with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      exact congrArg Nat.succ (checkProgramCompactionList_length h)

private theorem checkProgramCompactionList_getElem? :
    ∀ {sps : List CompactionSpec} {bs : List Body},
      checkProgramCompactionList sps bs = true →
      ∀ (defId : DefId) (b : Body) (sp : CompactionSpec),
        Trusted.MirSemantics.getElem? bs defId = some b →
        Trusted.MirSemantics.getElem? sps defId = some sp →
        ValidBodyCompaction b sp
  | [], _, _, _, _, _, _, hsp => by cases hsp
  | _ :: _, [], _, _, _, _, hGet, _ => by cases hGet
  | sp :: sps, b :: bs, h, 0, b', sp', hb, hsp => by
    injection hb with hbEq; subst hbEq
    injection hsp with hspEq; subst hspEq
    change (checkBodyCompaction b sp && checkProgramCompactionList sps bs) = true at h
    cases h1 : checkBodyCompaction b sp with
    | false => rw [h1] at h; cases h
    | true => exact validBodyCompaction_of_check h1
  | sp :: sps, b :: bs, h, n + 1, b', sp', hb, hsp => by
    change (checkBodyCompaction b sp && checkProgramCompactionList sps bs) = true at h
    cases h1 : checkBodyCompaction b sp with
    | false => rw [h1] at h; cases h
    | true =>
      rw [h1] at h
      exact checkProgramCompactionList_getElem? h n b' sp' hb hsp

/-- Soundness of the whole-program boolean validator `checkProgramCompaction`. -/
theorem validProgramCompaction_of_check {specs : List CompactionSpec} {pSrc : Program}
    (h : checkProgramCompaction specs pSrc = true) :
    ValidProgramCompaction specs pSrc :=
  ⟨checkProgramCompactionList_length h, checkProgramCompactionList_getElem? h⟩

/-! ### Program / Body Lookup and Static Entry Equivalence -/

private theorem getElem?_compactBodyList_some :
    ∀ {specs : List CompactionSpec} {bs : List Body} {d : DefId} {b : Body} {sp : CompactionSpec},
      Trusted.MirSemantics.getElem? bs d = some b →
      Trusted.MirSemantics.getElem? specs d = some sp →
      Trusted.MirSemantics.getElem? (compactBodyList specs bs) d = some (compactBody sp b)
  | [], _, _, _, _, _, hsp => by cases hsp
  | _, [], _, _, _, hb, _ => by cases hb
  | _ :: _, _ :: _, 0, _, _, hb, hsp => by
    injection hb with hbEq; subst hbEq
    injection hsp with hspEq; subst hspEq
    rfl
  | _ :: sps, _ :: bs, d + 1, b, sp, hb, hsp =>
    getElem?_compactBodyList_some (specs := sps) (bs := bs) (d := d) hb hsp

private theorem getElem?_compactBodyList_iff {specs : List CompactionSpec} {bs : List Body}
    (hLen : specs.length = bs.length) (d : DefId) :
    (match Trusted.MirSemantics.getElem? bs d, Trusted.MirSemantics.getElem? specs d with
     | some b, some sp =>
       Trusted.MirSemantics.getElem? (compactBodyList specs bs) d = some (compactBody sp b)
     | _, _ =>
       Trusted.MirSemantics.getElem? bs d = none ∧
       Trusted.MirSemantics.getElem? (compactBodyList specs bs) d = none) := by
  induction specs generalizing bs d with
  | nil =>
    cases bs with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => cases hLen
  | cons sp sps ih =>
    cases bs with
    | nil => cases hLen
    | cons b bs =>
      cases d with
      | zero => exact rfl
      | succ d =>
        exact ih (Nat.succ.inj hLen) d

private theorem getElem?_compactBasicBlockList :
    ∀ (smap : List Nat) (bbs : List BasicBlock) (i : Nat),
      Trusted.MirSemantics.getElem? (compactBasicBlockList smap bbs) i =
        match Trusted.MirSemantics.getElem? bbs i with
        | some bb => some (compactBasicBlock smap bb)
        | none => none
  | _, [], _ => rfl
  | _, _ :: _, 0 => rfl
  | smap, _ :: bbs, i + 1 => getElem?_compactBasicBlockList smap bbs i

private theorem compactBasicBlockList_isEmpty (smap : List Nat) :
    ∀ (bbs : List BasicBlock), (compactBasicBlockList smap bbs).isEmpty = bbs.isEmpty
  | [] => rfl
  | _ :: _ => rfl

private theorem compactBasicBlockList_length (smap : List Nat) :
    ∀ (bbs : List BasicBlock), (compactBasicBlockList smap bbs).length = bbs.length
  | [] => rfl
  | _ :: bbs => congrArg Nat.succ (compactBasicBlockList_length smap bbs)

private theorem compactBodyList_length :
    ∀ (specs : List CompactionSpec) (bs : List Body),
      specs.length = bs.length → (compactBodyList specs bs).length = bs.length
  | [], [], _ => rfl
  | _ :: sps, _ :: bs, h => congrArg Nat.succ (compactBodyList_length sps bs (Nat.succ.inj h))

private theorem compactStatements_any_storageMarker (smap : List Nat) (k : LocalId) :
    ∀ (stmts : List StatementKind),
      (compactStatements smap stmts).any (stmtHasStorageMarker k) = false
  | [] => rfl
  | .nop :: rest => compactStatements_any_storageMarker smap k rest
  | .storageLive _ :: rest => compactStatements_any_storageMarker smap k rest
  | .storageDead _ :: rest => compactStatements_any_storageMarker smap k rest
  | .assign _ _ :: rest => by
    change (false || (compactStatements smap rest).any (stmtHasStorageMarker k)) = false
    exact compactStatements_any_storageMarker smap k rest
  | .unsupported :: rest => by
    change (false || (compactStatements smap rest).any (stmtHasStorageMarker k)) = false
    exact compactStatements_any_storageMarker smap k rest

private theorem hasStorageAnnotation_compactBody_false (spec : CompactionSpec)
    (b : Body) (k : LocalId) :
    hasStorageAnnotation (compactBody spec b) k = false := by
  unfold hasStorageAnnotation compactBody
  dsimp only
  induction b.basicBlocks with
  | nil => rfl
  | cons bb bbs ih =>
    change ((compactStatements spec.slotMap bb.statements).any (stmtHasStorageMarker k) ||
      (compactBasicBlockList spec.slotMap bbs).any
        (fun bb => bb.statements.any (stmtHasStorageMarker k))) = false
    rw [compactStatements_any_storageMarker, ih]
    rfl

private theorem compactStatements_all_of_nonmarker (smap : List Nat)
    (f : StatementKind → Bool)
    (hfAssign : ∀ dst rv, f (.assign dst rv) = true)
    (hfUnsup : f .unsupported = true) :
    ∀ ss : List StatementKind, (compactStatements smap ss).all f = true
  | [] => rfl
  | .nop :: ss => compactStatements_all_of_nonmarker smap f hfAssign hfUnsup ss
  | .storageLive _ :: ss => compactStatements_all_of_nonmarker smap f hfAssign hfUnsup ss
  | .storageDead _ :: ss => compactStatements_all_of_nonmarker smap f hfAssign hfUnsup ss
  | .assign dst rv :: ss => by
    change (f (.assign (remapPlace smap dst) (remapRvalue smap rv)) &&
      (compactStatements smap ss).all f) = true
    rw [hfAssign, compactStatements_all_of_nonmarker smap f hfAssign hfUnsup ss]
    rfl
  | .unsupported :: ss => by
    change (f .unsupported && (compactStatements smap ss).all f) = true
    rw [hfUnsup, compactStatements_all_of_nonmarker smap f hfAssign hfUnsup ss]
    rfl

private theorem storageAnnotationsInBounds_compactBody (spec : CompactionSpec) (b : Body) :
    storageAnnotationsInBounds (compactBody spec b) = true := by
  unfold storageAnnotationsInBounds compactBody
  apply list_all_of_getElem?
  intro bbIdx bb hBb
  rw [getElem?_compactBasicBlockList] at hBb
  cases hSrcBb : Trusted.MirSemantics.getElem? b.basicBlocks bbIdx with
  | none => rw [hSrcBb] at hBb; cases hBb
  | some bbSrc =>
    rw [hSrcBb] at hBb
    injection hBb with hBbEq
    subst hBbEq
    exact compactStatements_all_of_nonmarker spec.slotMap _ (fun _ _ => rfl) rfl bbSrc.statements

private theorem storageAnnotationsInBounds_src_of_dead {mask : List Bool} {bSrc : Body}
    (hDead : StorageMarkersOnlyOnDead mask bSrc.locals.length bSrc) :
    storageAnnotationsInBounds bSrc = true := by
  unfold StorageMarkersOnlyOnDead storageMarkersOnlyOnDeadBool at hDead
  unfold storageAnnotationsInBounds
  apply list_all_of_getElem?
  intro bbIdx bb hbb
  have hbbAll := list_all_getElem? _ hDead bbIdx bb hbb
  apply list_all_of_getElem?
  intro sIdx stmt hstmt
  have hst := list_all_getElem? _ hbbAll sIdx stmt hstmt
  cases stmt with
  | assign _ _ | nop | unsupported => rfl
  | storageLive id =>
    change (Nat.blt id bSrc.locals.length && !(isLiveLocal mask id)) = true at hst
    cases hBlt : Nat.blt id bSrc.locals.length with
    | false => rw [hBlt] at hst; cases hst
    | true => exact hBlt
  | storageDead id =>
    change (!Nat.beq id 0 && Nat.blt id bSrc.locals.length && !(isLiveLocal mask id)) = true at hst
    cases hNz : !Nat.beq id 0 with
    | false => rw [hNz] at hst; cases hst
    | true =>
      rw [hNz] at hst
      cases hBlt : Nat.blt id bSrc.locals.length with
      | false => rw [hBlt] at hst; cases hst
      | true => exact hBlt

private theorem hasStorageAnnotation_src_live_false {mask : List Bool} {bSrc : Body}
    (hDead : StorageMarkersOnlyOnDead mask bSrc.locals.length bSrc)
    {i : LocalId} (hLive : isLiveLocal mask i = true) :
    hasStorageAnnotation bSrc i = false := by
  unfold StorageMarkersOnlyOnDead storageMarkersOnlyOnDeadBool at hDead
  unfold hasStorageAnnotation
  apply list_any_false_of_getElem?
  intro bbIdx bb hbb
  have hbbAll := list_all_getElem? _ hDead bbIdx bb hbb
  apply list_any_false_of_getElem?
  intro sIdx stmt hstmt
  have hst := list_all_getElem? _ hbbAll sIdx stmt hstmt
  cases stmt with
  | assign _ _ | nop | unsupported => rfl
  | storageLive id =>
    change (Nat.blt id bSrc.locals.length && !(isLiveLocal mask id)) = true at hst
    change Nat.beq id i = false
    cases hid : Nat.beq id i with
    | false => rfl
    | true =>
      have hEq := nat_beq_eq hid
      subst hEq
      rw [hLive] at hst
      cases hBlt : Nat.blt id bSrc.locals.length <;> rw [hBlt] at hst <;> cases hst
  | storageDead id =>
    change (!Nat.beq id 0 && Nat.blt id bSrc.locals.length && !(isLiveLocal mask id)) = true at hst
    change Nat.beq id i = false
    cases hid : Nat.beq id i with
    | false => rfl
    | true =>
      have hEq := nat_beq_eq hid
      subst hEq
      rw [hLive] at hst
      cases hNz : !Nat.beq id 0 <;> cases hBlt : Nat.blt id bSrc.locals.length <;>
        rw [hNz, hBlt] at hst <;> cases hst

private theorem getElem?_initLocalsLoop (body : Body) (args : List Val) :
    ∀ (base : Nat) (tys : List MirTy) (k : Nat),
      Trusted.MirSemantics.getElem? (initLocalsLoop body args base tys) k =
        match Trusted.MirSemantics.getElem? tys k with
        | none => none
        | some ty =>
          let idx := base + k
          some (if Nat.beq idx 0 then liveUninitSlot ty
                else if Nat.ble idx body.argumentCount then
                  match Trusted.MirSemantics.getElem? args (idx - 1) with
                  | some v => .live (some v)
                  | none => .dead
                else if hasStorageAnnotation body idx then .dead
                else liveUninitSlot ty)
  | _, [], _ => rfl
  | base, ty :: rest, 0 => by
    rw [Nat.add_zero]
    rfl
  | base, ty :: rest, k + 1 => by
    have ih := getElem?_initLocalsLoop body args (base + 1) rest k
    have hAssoc : base + 1 + k = base + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    change Trusted.MirSemantics.getElem? (initLocalsLoop body args (base + 1) rest) k = _
    rw [ih, hAssoc]
    rfl

private theorem initLocalsLoop_length (body : Body) (args : List Val) :
    ∀ (base : Nat) (tys : List MirTy),
      (initLocalsLoop body args base tys).length = tys.length
  | _, [] => rfl
  | base, _ :: rest => congrArg Nat.succ (initLocalsLoop_length body args (base + 1) rest)

/-- Live slot equivalence invariant relating `srcSlots` and `tgtSlots` under
mask `mask` and renumbering `smap`. -/
def LiveSlotsMatch (mask : List Bool) (smap : List Nat)
    (srcSlots tgtSlots : List LocalSlot) : Prop :=
  srcSlots.length = mask.length ∧
  ∀ i : LocalId, isLiveLocal mask i = true →
    Trusted.MirSemantics.getElem? tgtSlots (mapLocal smap i) =
      Trusted.MirSemantics.getElem? srcSlots i

private theorem mapLocal_gt_argc_of_live_gt {argc : Nat} {spec : CompactionSpec}
    (hAbi : PreservesAbiSlots argc spec)
    (hInj : InjectiveOnLive spec)
    {i : LocalId} (hiLive : isLiveLocal spec.liveMask i = true)
    (hiGt : argc < i) :
    argc < mapLocal spec.slotMap i := by
  cases Nat.lt_or_ge argc (mapLocal spec.slotMap i) with
  | inl hlt => exact hlt
  | inr hle =>
    let ⟨hjLive, hjMap⟩ := hAbi.2 (mapLocal spec.slotMap i) hle
    have hEq : i = mapLocal spec.slotMap i :=
      hInj i (mapLocal spec.slotMap i) hiLive hjLive hjMap.symm
    rw [hEq] at hiGt
    exact False.elim (Nat.not_lt_of_ge hle hiGt)

private theorem initLocalsLoop_liveSlotsMatch {bSrc : Body} {spec : CompactionSpec}
    (hAbi : PreservesAbiSlots bSrc.argumentCount spec)
    (hInj : InjectiveOnLive spec)
    (hTy : ValidTargetTypes bSrc spec)
    (hDead : StorageMarkersOnlyOnDead spec.liveMask bSrc.locals.length bSrc)
    (args : List Val) :
    LiveSlotsMatch spec.liveMask spec.slotMap
      (initLocalsLoop bSrc args 0 bSrc.locals)
      (initLocalsLoop (compactBody spec bSrc) args 0 spec.targetLocals) := by
  refine ⟨?_, ?_⟩
  · rw [initLocalsLoop_length, hTy.1]
  · intro i hiLive
    have hiLt : i < bSrc.locals.length := by
      rw [← hTy.1]
      exact isLiveLocal_eq_true_lt hiLive
    let ⟨srcTy, hSrcTy⟩ := getElem?_lt_some bSrc.locals hiLt
    have hTgtTy : Trusted.MirSemantics.getElem? spec.targetLocals (mapLocal spec.slotMap i) =
        some srcTy := by
      rw [(hTy.2.2.2.2 i hiLive).2]
      exact hSrcTy
    rw [getElem?_initLocalsLoop, getElem?_initLocalsLoop, hSrcTy, hTgtTy]
    dsimp only
    rw [Nat.zero_add, Nat.zero_add]
    cases Nat.eq_or_lt_of_le (Nat.zero_le i) with
    | inl hi0 =>
      subst hi0
      have hMap0 : mapLocal spec.slotMap 0 = 0 := (hAbi.2 0 (Nat.zero_le _)).2
      rw [hMap0]
      rfl
    | inr hiPos =>
      cases Nat.lt_or_ge bSrc.argumentCount i with
      | inr hiLeArg =>
        have hMapI : mapLocal spec.slotMap i = i := (hAbi.2 i hiLeArg).2
        rw [hMapI]
        have hNe0 : Nat.beq i 0 = false := by
          cases i with
          | zero => cases hiPos
          | succ _ => rfl
        have hBleSrc : Nat.ble i bSrc.argumentCount = true := nat_ble_true_iff.mpr hiLeArg
        have hBleTgt : Nat.ble i (compactBody spec bSrc).argumentCount = true := hBleSrc
        rw [bool_ite_neg hNe0, bool_ite_neg hNe0, bool_ite_pos hBleTgt, bool_ite_pos hBleSrc]
      | inl hiGtArg =>
        have hMapGt : bSrc.argumentCount < mapLocal spec.slotMap i :=
          mapLocal_gt_argc_of_live_gt hAbi hInj hiLive hiGtArg
        have hNeSrc0 : Nat.beq i 0 = false := by
          cases i with
          | zero => cases hiPos
          | succ _ => rfl
        have hNeTgt0 : Nat.beq (mapLocal spec.slotMap i) 0 = false := by
          cases hM : mapLocal spec.slotMap i with
          | zero =>
            rw [hM] at hMapGt
            cases hMapGt
          | succ _ => rfl
        have hBleSrc : Nat.ble i bSrc.argumentCount = false :=
          nat_ble_false_iff.mpr hiGtArg
        have hBleTgt : Nat.ble (mapLocal spec.slotMap i) (compactBody spec bSrc).argumentCount = false :=
          nat_ble_false_iff.mpr hMapGt
        have hNoAnnSrc : hasStorageAnnotation bSrc i = false :=
          hasStorageAnnotation_src_live_false hDead hiLive
        have hNoAnnTgt : hasStorageAnnotation (compactBody spec bSrc) (mapLocal spec.slotMap i) = false :=
          hasStorageAnnotation_compactBody_false spec bSrc (mapLocal spec.slotMap i)
        rw [bool_ite_neg hNeTgt0, bool_ite_neg hNeSrc0, bool_ite_neg hBleTgt, bool_ite_neg hBleSrc,
          bool_ite_neg hNoAnnTgt, bool_ite_neg hNoAnnSrc]

private theorem take_drop_paramTys_eq {bSrc : Body} {spec : CompactionSpec}
    (hAbi : PreservesAbiSlots bSrc.argumentCount spec)
    (hTy : ValidTargetTypes bSrc spec) :
    (spec.targetLocals.drop 1).take bSrc.argumentCount =
      (bSrc.locals.drop 1).take bSrc.argumentCount := by
  have hSrcLen : bSrc.argumentCount < bSrc.locals.length := by
    rw [← hTy.1]
    exact hAbi.1
  have hTgtLen : bSrc.argumentCount < spec.targetLocals.length := hTy.2.1
  cases hs : bSrc.locals with
  | nil => rw [hs] at hSrcLen; cases hSrcLen
  | cons s0 srest =>
    cases ht : spec.targetLocals with
    | nil => rw [ht] at hTgtLen; cases hTgtLen
    | cons t0 trest =>
      change trest.take bSrc.argumentCount = srest.take bSrc.argumentCount
      apply list_take_eq_of_getElem?
      · rw [ht] at hTgtLen
        exact Nat.le_of_succ_le_succ hTgtLen
      · rw [hs] at hSrcLen
        exact Nat.le_of_succ_le_succ hSrcLen
      · intro i hi
        have hiLe : i + 1 ≤ bSrc.argumentCount := hi
        let ⟨hiLive, hiMap⟩ := hAbi.2 (i + 1) hiLe
        have hEq := (hTy.2.2.2.2 (i + 1) hiLive).2
        rw [hiMap, hs, ht] at hEq
        exact hEq

/-- Frame relation between a source state `sSrc` and a compacted target state
`sTgt`. -/
def CompactedStateRel (specs : List CompactionSpec) (pSrc : Program)
    (sSrc sTgt : State) : Prop :=
  sSrc.callerMem = sTgt.callerMem ∧
  ∃ (fSrc fTgt : FrameState) (bSrc : Body) (spec : CompactionSpec),
    sSrc.frames = [fSrc] ∧
    sTgt.frames = [fTgt] ∧
    fSrc.defId = fTgt.defId ∧
    fSrc.blockIdx = fTgt.blockIdx ∧
    Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
    Trusted.MirSemantics.getElem? specs fSrc.defId = some spec ∧
    LiveSlotsMatch spec.liveMask spec.slotMap fSrc.locals fTgt.locals ∧
    ∀ bbSrc : BasicBlock,
      Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
      fSrc.stmtIdx ≤ bbSrc.statements.length ∧
      fTgt.stmtIdx ≤ (compactBasicBlock spec.slotMap bbSrc).statements.length ∧
      compactStatements spec.slotMap (bbSrc.statements.drop fSrc.stmtIdx) =
        (compactBasicBlock spec.slotMap bbSrc).statements.drop fTgt.stmtIdx

private theorem initState_compact_equiv {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query) :
    match initState pSrc q, initState (compactProgram specs pSrc) q with
    | .error k1, .error k2 => k1 = k2
    | .ok sSrc, .ok sTgt => CompactedStateRel specs pSrc sSrc sTgt
    | _, _ => False := by
  unfold initState compactProgram
  dsimp only
  have hFalse : (false : Bool) = false := rfl
  have hTrue : (true : Bool) = true := rfl
  cases hPW : (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) with
  | true => rfl
  | false =>
    repeat rw [bool_ite_neg hFalse]
    cases hMem : !q.callerMem.allocations.isEmpty with
    | true => rfl
    | false =>
      repeat rw [bool_ite_neg hFalse]
      have hSpec := getElem?_compactBodyList_iff hValid.1 pSrc.entryDefId
      cases hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
      | none =>
        rw [hBSrc] at hSpec
        dsimp only at hSpec; dsimp only
        rw [hSpec.2]
      | some bSrc =>
        cases hSp : Trusted.MirSemantics.getElem? specs pSrc.entryDefId with
        | none =>
          have hGe := getElem?_none_iff.mp hSp
          have hLt := getElem?_eq_some_lt hBSrc
          rw [hValid.1] at hGe
          exact False.elim (Nat.not_lt_of_ge hGe hLt)
        | some spec =>
          rw [hBSrc, hSp] at hSpec
          dsimp only at hSpec; dsimp only
          rw [hSpec]
          dsimp only
          have hBodyValid := hValid.2 pSrc.entryDefId bSrc spec hBSrc hSp
          let ⟨hAbi, hInj, hTy, hRef, hDead⟩ := hBodyValid
          have hEmpty : (compactBody spec bSrc).basicBlocks.isEmpty = bSrc.basicBlocks.isEmpty :=
            compactBasicBlockList_isEmpty spec.slotMap bSrc.basicBlocks
          have hArgSrc : Nat.blt bSrc.argumentCount bSrc.locals.length = true := by
            apply nat_blt_true_iff.mpr
            rw [← hTy.1]
            exact hAbi.1
          have hArgTgt : Nat.blt (compactBody spec bSrc).argumentCount
              (compactBody spec bSrc).locals.length = true :=
            nat_blt_true_iff.mpr hTy.2.1
          have hAnnSrc : storageAnnotationsInBounds bSrc = true :=
            storageAnnotationsInBounds_src_of_dead hDead
          have hAnnTgt : storageAnnotationsInBounds (compactBody spec bSrc) = true :=
            storageAnnotationsInBounds_compactBody spec bSrc
          have hParamEq : ((compactBody spec bSrc).locals.drop 1).take
              (compactBody spec bSrc).argumentCount =
              (bSrc.locals.drop 1).take bSrc.argumentCount :=
            take_drop_paramTys_eq hAbi hTy
          have hLocTgt : (compactBody spec bSrc).locals.all isSupportedScalarOrUnitTy = true :=
            hTy.2.2.1
          have hLocSrc : bSrc.locals.all isSupportedScalarOrUnitTy = true :=
            hTy.2.2.2.1
          rw [hEmpty, hArgSrc, hArgTgt, hAnnSrc, hAnnTgt, hLocTgt, hLocSrc, hParamEq]
          repeat rw [bool_ite_neg hFalse]
          cases hIsEmp : bSrc.basicBlocks.isEmpty with
          | true =>
            repeat rw [bool_ite_pos hTrue]
          | false =>
            repeat rw [bool_ite_neg hFalse]
            cases hArgsOk : checkArgsMatch q.args ((bSrc.locals.drop 1).take bSrc.argumentCount) with
            | false =>
              repeat rw [bool_ite_pos hTrue]
              rfl
            | true =>
              repeat rw [bool_ite_neg hFalse]
              refine ⟨rfl, _, _, bSrc, spec, rfl, rfl, rfl, rfl, hBSrc, hSp,
                initLocalsLoop_liveSlotsMatch hAbi hInj hTy hDead q.args, ?_⟩
              intro bbSrc _
              exact ⟨Nat.zero_le _, Nat.zero_le _, rfl⟩

/-! ### Operand, Rvalue, WritePlace, Statement, and Terminator Commutation -/

private theorem evalOperandToSlot_compact {bSrc : Body} {spec : CompactionSpec}
    (hInj : InjectiveOnLive spec)
    (hTy : ValidTargetTypes bSrc spec)
    {srcSlots tgtSlots : List LocalSlot}
    (hMatch : LiveSlotsMatch spec.liveMask spec.slotMap srcSlots tgtSlots)
    {op : Operand} (hOp : operandLocalsInMask spec.liveMask op = true) :
    match evalOperandToSlot bSrc.locals srcSlots op,
        evalOperandToSlot spec.targetLocals tgtSlots (remapOperand spec.slotMap op) with
    | .error k1, .error k2 => k1 = k2
    | .ok (ty1, ov1, srcSlots'), .ok (ty2, ov2, tgtSlots') =>
      ty1 = ty2 ∧ ov1 = ov2 ∧ LiveSlotsMatch spec.liveMask spec.slotMap srcSlots' tgtSlots'
    | _, _ => False := by
  cases op with
  | constant c =>
    unfold evalOperandToSlot remapOperand
    dsimp only
    cases evalConstLit c.ty c.lit with
    | error _ => rfl
    | ok _ => exact ⟨rfl, rfl, hMatch⟩
  | copy place =>
    change isLiveLocal spec.liveMask place.localId = true at hOp
    unfold evalOperandToSlot remapOperand remapPlace
    dsimp only
    cases hProj : !place.projection.isEmpty with
    | true => rfl
    | false =>
      have hTyEq := (hTy.2.2.2.2 place.localId hOp).2
      have hSlotEq := hMatch.2 place.localId hOp
      rw [hTyEq, hSlotEq]
      cases Trusted.MirSemantics.getElem? bSrc.locals place.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? srcSlots place.localId with
        | none => rfl
        | some slot =>
          cases slot with
          | dead => rfl
          | live ov => exact ⟨rfl, rfl, hMatch⟩
  | move place =>
    change isLiveLocal spec.liveMask place.localId = true at hOp
    unfold evalOperandToSlot remapOperand remapPlace
    dsimp only
    cases hProj : !place.projection.isEmpty with
    | true => rfl
    | false =>
      have hTyEq := (hTy.2.2.2.2 place.localId hOp).2
      have hSlotEq := hMatch.2 place.localId hOp
      rw [hTyEq, hSlotEq]
      cases hBL : Trusted.MirSemantics.getElem? bSrc.locals place.localId with
      | none => rfl
      | some ty =>
        cases hSL : Trusted.MirSemantics.getElem? srcSlots place.localId with
        | none => rfl
        | some slot =>
          cases slot with
          | dead => rfl
          | live ov =>
            have hSrcLt : place.localId < srcSlots.length := getElem?_eq_some_lt hSL
            have hTgtSome : Trusted.MirSemantics.getElem? tgtSlots (mapLocal spec.slotMap place.localId) =
                some (.live ov) := by
              rw [hSlotEq, hSL]
            have hTgtLt : mapLocal spec.slotMap place.localId < tgtSlots.length :=
              getElem?_eq_some_lt hTgtSome
            dsimp only
            let ⟨src', hSetSrc, _⟩ := setElem?_lt_some srcSlots (liveUninitSlot ty) hSrcLt
            let ⟨tgt', hSetTgt, _⟩ := setElem?_lt_some tgtSlots (liveUninitSlot ty) hTgtLt
            rw [hSetSrc, hSetTgt]
            refine ⟨rfl, rfl, (setElem?_some_length hSetSrc).trans hMatch.1, ?_⟩
            intro j hjLive
            cases hEqJ : Nat.beq place.localId j with
            | true =>
              have hjEq := nat_beq_eq hEqJ
              subst hjEq
              rw [getElem?_setElem?_same hSetSrc, getElem?_setElem?_same hSetTgt]
            | false =>
              have hNeSrc : place.localId ≠ j := fun hEq => by
                rw [hEq, nat_beq_refl] at hEqJ
                cases hEqJ
              have hNeTgt : mapLocal spec.slotMap place.localId ≠ mapLocal spec.slotMap j :=
                fun hEq => hNeSrc (hInj place.localId j hOp hjLive hEq)
              rw [getElem?_setElem?_ne hNeSrc hSetSrc, getElem?_setElem?_ne hNeTgt hSetTgt]
              exact hMatch.2 j hjLive

private theorem evalPrimitiveOperand_compact {bSrc : Body} {spec : CompactionSpec}
    (hInj : InjectiveOnLive spec)
    (hTy : ValidTargetTypes bSrc spec)
    {srcSlots tgtSlots : List LocalSlot}
    (hMatch : LiveSlotsMatch spec.liveMask spec.slotMap srcSlots tgtSlots)
    {op : Operand} (hOp : operandLocalsInMask spec.liveMask op = true) :
    match evalPrimitiveOperand bSrc.locals srcSlots op,
        evalPrimitiveOperand spec.targetLocals tgtSlots (remapOperand spec.slotMap op) with
    | .error k1, .error k2 => k1 = k2
    | .ok (v1, srcSlots'), .ok (v2, tgtSlots') =>
      v1 = v2 ∧ LiveSlotsMatch spec.liveMask spec.slotMap srcSlots' tgtSlots'
    | _, _ => False := by
  unfold evalPrimitiveOperand
  have hSlot := evalOperandToSlot_compact hInj hTy hMatch hOp
  cases hSrc : evalOperandToSlot bSrc.locals srcSlots op with
  | error k1 =>
    cases hTgt : evalOperandToSlot spec.targetLocals tgtSlots (remapOperand spec.slotMap op) with
    | error k2 =>
      rw [hSrc, hTgt] at hSlot
      exact hSlot
    | ok p2 =>
      rw [hSrc, hTgt] at hSlot
      exact False.elim hSlot
  | ok p1 =>
    cases hTgt : evalOperandToSlot spec.targetLocals tgtSlots (remapOperand spec.slotMap op) with
    | error k2 =>
      rw [hSrc, hTgt] at hSlot
      exact False.elim hSlot
    | ok p2 =>
      rw [hSrc, hTgt] at hSlot
      dsimp only at hSlot
      let ⟨hTyEq, hOvEq, hMatch'⟩ := hSlot
      dsimp only
      rw [← hTyEq, ← hOvEq]
      cases !isPrimitiveReadableTy p1.1 with
      | true => rfl
      | false =>
        cases p1.2.1 with
        | none => rfl
        | some v => exact ⟨rfl, hMatch'⟩

private theorem evalRvalue_compact {bSrc : Body} {spec : CompactionSpec}
    (hInj : InjectiveOnLive spec)
    (hTy : ValidTargetTypes bSrc spec)
    {srcSlots tgtSlots : List LocalSlot}
    (hMatch : LiveSlotsMatch spec.liveMask spec.slotMap srcSlots tgtSlots)
    (dstTy : MirTy) {rv : Rvalue}
    (hRv : rvalueLocalsInMask spec.liveMask rv = true) :
    match evalRvalue bSrc.locals srcSlots dstTy rv,
        evalRvalue spec.targetLocals tgtSlots dstTy (remapRvalue spec.slotMap rv) with
    | .error k1, .error k2 => k1 = k2
    | .ok (v1, srcSlots'), .ok (v2, tgtSlots') =>
      v1 = v2 ∧ LiveSlotsMatch spec.liveMask spec.slotMap srcSlots' tgtSlots'
    | _, _ => False := by
  cases rv with
  | use op =>
    change operandLocalsInMask spec.liveMask op = true at hRv
    unfold evalRvalue remapRvalue
    dsimp only
    have hSlot := evalOperandToSlot_compact hInj hTy hMatch hRv
    cases hSrc : evalOperandToSlot bSrc.locals srcSlots op with
    | error k1 =>
      cases hTgt : evalOperandToSlot spec.targetLocals tgtSlots (remapOperand spec.slotMap op) with
      | error k2 =>
        rw [hSrc, hTgt] at hSlot
        exact hSlot
      | ok p2 =>
        rw [hSrc, hTgt] at hSlot
        exact False.elim hSlot
    | ok p1 =>
      cases hTgt : evalOperandToSlot spec.targetLocals tgtSlots (remapOperand spec.slotMap op) with
      | error k2 =>
        rw [hSrc, hTgt] at hSlot
        exact False.elim hSlot
      | ok p2 =>
        rw [hSrc, hTgt] at hSlot
        dsimp only at hSlot; dsimp only
        let ⟨hTyEq, hOvEq, hMatch'⟩ := hSlot
        rw [← hTyEq, ← hOvEq]
        cases !MirTy.beq p1.1 dstTy with
        | true => rfl
        | false =>
          cases p1.2.1 with
          | none => rfl
          | some v => exact ⟨rfl, hMatch'⟩
  | binaryOp op lhs rhs =>
    change (operandLocalsInMask spec.liveMask lhs && operandLocalsInMask spec.liveMask rhs) = true at hRv
    cases hLhsMask : operandLocalsInMask spec.liveMask lhs with
    | false => rw [hLhsMask] at hRv; cases hRv
    | true =>
      rw [hLhsMask] at hRv
      unfold evalRvalue remapRvalue
      dsimp only
      have hL := evalPrimitiveOperand_compact hInj hTy hMatch hLhsMask
      cases hSrc1 : evalPrimitiveOperand bSrc.locals srcSlots lhs with
      | error k1 =>
        cases hTgt1 : evalPrimitiveOperand spec.targetLocals tgtSlots (remapOperand spec.slotMap lhs) with
        | error k2 =>
          rw [hSrc1, hTgt1] at hL
          exact hL
        | ok p2 =>
          rw [hSrc1, hTgt1] at hL
          exact False.elim hL
      | ok p1 =>
        cases hTgt1 : evalPrimitiveOperand spec.targetLocals tgtSlots (remapOperand spec.slotMap lhs) with
        | error k2 =>
          rw [hSrc1, hTgt1] at hL
          exact False.elim hL
        | ok p2 =>
          rw [hSrc1, hTgt1] at hL
          dsimp only at hL; dsimp only
          let ⟨hv1, hMatch1⟩ := hL
          have hR := evalPrimitiveOperand_compact hInj hTy hMatch1 hRv
          cases hSrc2 : evalPrimitiveOperand bSrc.locals p1.2 rhs with
          | error k1 =>
            cases hTgt2 : evalPrimitiveOperand spec.targetLocals p2.2 (remapOperand spec.slotMap rhs) with
            | error k2 =>
              rw [hSrc2, hTgt2] at hR
              exact hR
            | ok q2 =>
              rw [hSrc2, hTgt2] at hR
              exact False.elim hR
          | ok q1 =>
            cases hTgt2 : evalPrimitiveOperand spec.targetLocals p2.2 (remapOperand spec.slotMap rhs) with
            | error k2 =>
              rw [hSrc2, hTgt2] at hR
              exact False.elim hR
            | ok q2 =>
              rw [hSrc2, hTgt2] at hR
              dsimp only at hR; dsimp only
              let ⟨hv2, hMatch2⟩ := hR
              rw [← hv1, ← hv2]
              cases evalBinOp op p1.1 q1.1 with
              | error _ => rfl
              | ok res => exact ⟨rfl, hMatch2⟩
  | unaryOp op x =>
    change operandLocalsInMask spec.liveMask x = true at hRv
    unfold evalRvalue remapRvalue
    dsimp only
    have hX := evalPrimitiveOperand_compact hInj hTy hMatch hRv
    cases hSrc : evalPrimitiveOperand bSrc.locals srcSlots x with
    | error k1 =>
      cases hTgt : evalPrimitiveOperand spec.targetLocals tgtSlots (remapOperand spec.slotMap x) with
      | error k2 =>
        rw [hSrc, hTgt] at hX
        exact hX
      | ok p2 =>
        rw [hSrc, hTgt] at hX
        exact False.elim hX
    | ok p1 =>
      cases hTgt : evalPrimitiveOperand spec.targetLocals tgtSlots (remapOperand spec.slotMap x) with
      | error k2 =>
        rw [hSrc, hTgt] at hX
        exact False.elim hX
      | ok p2 =>
        rw [hSrc, hTgt] at hX
        dsimp only at hX; dsimp only
        let ⟨hv, hMatch1⟩ := hX
        rw [← hv]
        cases evalUnOp op p1.1 with
        | error _ => rfl
        | ok res => exact ⟨rfl, hMatch1⟩
  | discriminant p =>
    change isLiveLocal spec.liveMask p.localId = true at hRv
    unfold evalRvalue remapRvalue remapPlace
    dsimp only
    cases !p.projection.isEmpty with
    | true => rfl
    | false =>
      have hTyEq := (hTy.2.2.2.2 p.localId hRv).2
      have hSlotEq := hMatch.2 p.localId hRv
      rw [hTyEq, hSlotEq]
      cases Trusted.MirSemantics.getElem? bSrc.locals p.localId with
      | none => rfl
      | some ty =>
        cases ty with
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
          cases Trusted.MirSemantics.getElem? srcSlots p.localId <;> rfl
        | enum ety =>
          cases Trusted.MirSemantics.getElem? srcSlots p.localId with
          | none => rfl
          | some slot =>
            dsimp only
            cases !enumAdmitted ety with
            | true => rfl
            | false =>
              cases ety.tagRepr <;> cases slot with
              | dead => rfl
              | live ov =>
                cases ov with
                | none =>
                  dsimp only
                  cases Trusted.MirSemantics.getElem? ety.discriminants 0 with
                  | none => rfl
                  | some _ => first | rfl | exact ⟨rfl, hMatch⟩
                | some v =>
                  cases v with
                  | enumVal ety' idx =>
                    dsimp only
                    cases (EnumTy.beq ety ety' && Nat.beq idx 0) <;>
                    cases (EnumTy.beq ety ety' && Nat.blt idx ety.discriminants.length) <;>
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;>
                    cases Trusted.MirSemantics.getElem? ety.discriminants idx <;>
                    first | rfl | exact ⟨rfl, hMatch⟩
                  | scalar _ | ptr _ | bool _ | unit | tuple _ | bytes _ =>
                    rfl
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => rfl

private theorem writePlace_compact {spec : CompactionSpec}
    (hInj : InjectiveOnLive spec)
    {srcSlots tgtSlots : List LocalSlot}
    (hMatch : LiveSlotsMatch spec.liveMask spec.slotMap srcSlots tgtSlots)
    {dst : LocalId} (hLive : isLiveLocal spec.liveMask dst = true)
    (dstTy : MirTy) (val : Val) :
    match writePlace srcSlots dst dstTy val,
        writePlace tgtSlots (mapLocal spec.slotMap dst) dstTy val with
    | .error k1, .error k2 => k1 = k2
    | .ok srcSlots', .ok tgtSlots' =>
      LiveSlotsMatch spec.liveMask spec.slotMap srcSlots' tgtSlots'
    | _, _ => False := by
  unfold writePlace
  cases !checkVal val dstTy with
  | true => rfl
  | false =>
    have hSlotEq : Trusted.MirSemantics.getElem? tgtSlots (mapLocal spec.slotMap dst) =
        Trusted.MirSemantics.getElem? srcSlots dst :=
      hMatch.2 dst hLive
    rw [hSlotEq]
    cases hGet : Trusted.MirSemantics.getElem? srcSlots dst with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | live _ =>
        dsimp only
        have hSrcLt : dst < srcSlots.length := getElem?_eq_some_lt hGet
        have hTgtLt : mapLocal spec.slotMap dst < tgtSlots.length := by
          rw [← hSlotEq] at hGet
          exact getElem?_eq_some_lt hGet
        let ⟨srcSlots', hSetSrc, _⟩ := setElem?_lt_some srcSlots (.live (some val)) hSrcLt
        let ⟨tgtSlots', hSetTgt, _⟩ := setElem?_lt_some tgtSlots (.live (some val)) hTgtLt
        rw [hSetSrc, hSetTgt]
        dsimp only
        refine ⟨?_, ?_⟩
        · rw [setElem?_some_length hSetSrc, hMatch.1]
        · intro j hjLive
          cases hEqJ : Nat.beq dst j with
          | true =>
            have hjEq := nat_beq_eq hEqJ
            subst hjEq
            rw [getElem?_setElem?_same hSetSrc, getElem?_setElem?_same hSetTgt]
          | false =>
            have hNeSrc : dst ≠ j := fun hEq => by
              rw [hEq, nat_beq_refl] at hEqJ
              cases hEqJ
            have hNeTgt : mapLocal spec.slotMap dst ≠ mapLocal spec.slotMap j :=
              fun hEq => hNeSrc (hInj dst j hLive hjLive hEq)
            rw [getElem?_setElem?_ne hNeSrc hSetSrc, getElem?_setElem?_ne hNeTgt hSetTgt]
            exact hMatch.2 j hjLive

/-- Predicate identifying source statements deleted by `R0 -> R3` compaction. -/
noncomputable def isStutterStmt : StatementKind → Bool
  | .nop | .storageLive _ | .storageDead _ => true
  | .assign _ _ | .unsupported => false

private theorem isStutterStmt_drop {smap : List Nat} {stmt : StatementKind}
    {rest : List StatementKind} (h : isStutterStmt stmt = true) :
    compactStatements smap (stmt :: rest) = compactStatements smap rest := by
  cases stmt with
  | nop | storageLive _ | storageDead _ => rfl
  | assign _ _ | unsupported => cases h

private theorem stmtStorageOnlyOnDead_implies_stutter_ok {bSrc : Body} {spec : CompactionSpec}
    (hDead : StorageMarkersOnlyOnDead spec.liveMask bSrc.locals.length bSrc)
    {bbIdx stmtIdx : Nat} {bbSrc : BasicBlock} {stmt : StatementKind}
    (hBb : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc)
    (hStmt : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx = some stmt) :
    stmtStorageOnlyOnDead spec.liveMask bSrc.locals.length stmt = true := by
  unfold StorageMarkersOnlyOnDead storageMarkersOnlyOnDeadBool at hDead
  have hBbAll := list_all_getElem? (fun bb => bb.statements.all (stmtStorageOnlyOnDead spec.liveMask bSrc.locals.length)) hDead bbIdx bbSrc hBb
  exact list_all_getElem? (stmtStorageOnlyOnDead spec.liveMask bSrc.locals.length) hBbAll stmtIdx stmt hStmt

private theorem stmtRefLocalsInMask_of_pos {bSrc : Body} {spec : CompactionSpec}
    (hRef : AllReferencedLocalsInLiveMask spec.liveMask bSrc)
    {bbIdx stmtIdx : Nat} {bbSrc : BasicBlock} {stmt : StatementKind}
    (hBb : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc)
    (hStmt : Trusted.MirSemantics.getElem? bbSrc.statements stmtIdx = some stmt) :
    stmtRefLocalsInMask spec.liveMask stmt = true := by
  unfold AllReferencedLocalsInLiveMask allReferencedLocalsInLiveMaskBool at hRef
  have hBbAll := list_all_getElem?
    (fun bb => bb.statements.all (stmtRefLocalsInMask spec.liveMask) && termLocalsInMask spec.liveMask bb.terminator)
    hRef bbIdx bbSrc hBb
  cases hStmts : bbSrc.statements.all (stmtRefLocalsInMask spec.liveMask) with
  | false =>
    rw [hStmts] at hBbAll
    cases hBbAll
  | true =>
    exact list_all_getElem? (stmtRefLocalsInMask spec.liveMask) hStmts stmtIdx stmt hStmt

private theorem termLocalsInMask_of_pos {bSrc : Body} {spec : CompactionSpec}
    (hRef : AllReferencedLocalsInLiveMask spec.liveMask bSrc)
    {bbIdx : Nat} {bbSrc : BasicBlock}
    (hBb : Trusted.MirSemantics.getElem? bSrc.basicBlocks bbIdx = some bbSrc) :
    termLocalsInMask spec.liveMask bbSrc.terminator = true := by
  unfold AllReferencedLocalsInLiveMask allReferencedLocalsInLiveMaskBool at hRef
  have hBbAll := list_all_getElem?
    (fun bb => bb.statements.all (stmtRefLocalsInMask spec.liveMask) && termLocalsInMask spec.liveMask bb.terminator)
    hRef bbIdx bbSrc hBb
  cases hStmts : bbSrc.statements.all (stmtRefLocalsInMask spec.liveMask) with
  | false =>
    rw [hStmts] at hBbAll
    cases hBbAll
  | true =>
    rw [hStmts] at hBbAll
    exact hBbAll

private theorem evalStatement_stutter_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {sSrc sTgt : State} (hRel : CompactedStateRel specs pSrc sSrc sTgt)
    {fSrc : FrameState} {bSrc : Body} {spec : CompactionSpec}
    (hFSrc : sSrc.frames = [fSrc])
    (hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc)
    (hSpec : Trusted.MirSemantics.getElem? specs fSrc.defId = some spec)
    {bbSrc : BasicBlock} {stmt : StatementKind}
    (hBb : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc)
    (hStmt : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx = some stmt)
    (hStutter : isStutterStmt stmt = true) :
    ∃ sSrc' : State,
      evalStatement bSrc fSrc sSrc.callerMem stmt = .step sSrc' ∧
      CompactedStateRel specs pSrc sSrc' sTgt ∧
      ∃ fSrc' : FrameState,
        sSrc'.frames = [fSrc'] ∧
        fSrc'.defId = fSrc.defId ∧
        fSrc'.blockIdx = fSrc.blockIdx ∧
        fSrc'.stmtIdx = fSrc.stmtIdx + 1 := by
  let ⟨hMem, fS, fT, bS, sp, hFS, hFT, hDef, hBlk, hBS, hSp, hMatch, hBlockInv⟩ := hRel
  rw [hFSrc] at hFS
  injection hFS with hFEq
  subst hFEq
  rw [hBSrc] at hBS
  injection hBS with hBEq
  subst hBEq
  rw [hSpec] at hSp
  injection hSp with hSpEq
  subst hSpEq
  let ⟨hAbi, hInj, hTy, hRef, hDead⟩ := hValid.2 fSrc.defId bSrc spec hBSrc hSpec
  have hMarker := stmtStorageOnlyOnDead_implies_stutter_ok hDead hBb hStmt
  let ⟨hSrcLe, hTgtLe, hDropEq⟩ := hBlockInv bbSrc hBb
  have hStmtLt : fSrc.stmtIdx < bbSrc.statements.length := getElem?_eq_some_lt hStmt
  cases stmt with
  | assign _ _ | unsupported => cases hStutter
  | nop =>
    refine ⟨{ frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1 }], callerMem := sSrc.callerMem }, rfl, ?_, { fSrc with stmtIdx := fSrc.stmtIdx + 1 }, rfl, rfl, rfl, rfl⟩
    refine ⟨hMem, _, fT, bSrc, spec, rfl, hFT, hDef, hBlk, hBSrc, hSpec, hMatch, ?_⟩
    intro bbSrc' hBb'
    rw [hBb] at hBb'
    injection hBb' with hBbEq
    subst hBbEq
    refine ⟨hStmtLt, hTgtLe, ?_⟩
    have hStepDrop : bbSrc.statements.drop fSrc.stmtIdx = StatementKind.nop :: bbSrc.statements.drop (fSrc.stmtIdx + 1) :=
      drop_getElem?_succ bbSrc.statements fSrc.stmtIdx StatementKind.nop hStmt
    rw [hStepDrop] at hDropEq
    exact hDropEq
  | storageLive id =>
    change (Nat.blt id bSrc.locals.length && !(isLiveLocal spec.liveMask id)) = true at hMarker
    cases hBlt : Nat.blt id bSrc.locals.length with
    | false =>
      rw [hBlt] at hMarker
      cases hMarker
    | true =>
      rw [hBlt] at hMarker
      have hidNotLive : isLiveLocal spec.liveMask id = false := by
        cases hL : isLiveLocal spec.liveMask id with
        | false => rfl
        | true => rw [hL] at hMarker; cases hMarker
      have hidLtBody : id < bSrc.locals.length := nat_blt_true_iff.mp hBlt
      have hidLtSlots : id < fSrc.locals.length := by
        rw [hMatch.1, hTy.1]
        exact hidLtBody
      let ⟨localTy, hGetTy⟩ := getElem?_lt_some bSrc.locals hidLtBody
      let ⟨locals', hSet, _⟩ := setElem?_lt_some fSrc.locals (liveUninitSlot localTy) hidLtSlots
      have hEval : evalStatement bSrc fSrc sSrc.callerMem (.storageLive id) =
          .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locals' }], callerMem := sSrc.callerMem } := by
        unfold evalStatement
        dsimp only
        rw [hGetTy]
        dsimp only
        rw [hSet]
      refine ⟨_, hEval, ?_, { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locals' }, rfl, rfl, rfl, rfl⟩
      refine ⟨hMem, _, fT, bSrc, spec, rfl, hFT, hDef, hBlk, hBSrc, hSpec, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [setElem?_some_length hSet, hMatch.1]
        · intro j hjLive
          have hNe : id ≠ j := fun hEq => by
            rw [hEq, hjLive] at hidNotLive
            cases hidNotLive
          rw [getElem?_setElem?_ne hNe hSet]
          exact hMatch.2 j hjLive
      · intro bbSrc' hBb'
        rw [hBb] at hBb'
        injection hBb' with hBbEq
        subst hBbEq
        refine ⟨hStmtLt, hTgtLe, ?_⟩
        have hStepDrop : bbSrc.statements.drop fSrc.stmtIdx = (.storageLive id) :: bbSrc.statements.drop (fSrc.stmtIdx + 1) :=
          drop_getElem?_succ bbSrc.statements fSrc.stmtIdx (.storageLive id) hStmt
        rw [hStepDrop] at hDropEq
        exact hDropEq
  | storageDead id =>
    change (!Nat.beq id 0 && Nat.blt id bSrc.locals.length && !(isLiveLocal spec.liveMask id)) = true at hMarker
    cases hZero : Nat.beq id 0 with
    | true =>
      rw [hZero] at hMarker
      cases hMarker
    | false =>
      rw [hZero] at hMarker
      cases hBlt : Nat.blt id bSrc.locals.length with
      | false =>
        rw [hBlt] at hMarker
        cases hMarker
      | true =>
        rw [hBlt] at hMarker
        have hidNotLive : isLiveLocal spec.liveMask id = false := by
          cases hL : isLiveLocal spec.liveMask id with
          | false => rfl
          | true => rw [hL] at hMarker; cases hMarker
        have hidLtBody : id < bSrc.locals.length := nat_blt_true_iff.mp hBlt
        have hidLtSlots : id < fSrc.locals.length := by
          rw [hMatch.1, hTy.1]
          exact hidLtBody
        let ⟨locals', hSet, _⟩ := setElem?_lt_some fSrc.locals .dead hidLtSlots
        have hEval : evalStatement bSrc fSrc sSrc.callerMem (.storageDead id) =
            .step { frames := [{ fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locals' }], callerMem := sSrc.callerMem } := by
          unfold evalStatement
          dsimp only
          rw [bool_ite_neg hZero, hSet]
        refine ⟨_, hEval, ?_, { fSrc with stmtIdx := fSrc.stmtIdx + 1, locals := locals' }, rfl, rfl, rfl, rfl⟩
        refine ⟨hMem, _, fT, bSrc, spec, rfl, hFT, hDef, hBlk, hBSrc, hSpec, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · rw [setElem?_some_length hSet, hMatch.1]
          · intro j hjLive
            have hNe : id ≠ j := fun hEq => by
              rw [hEq, hjLive] at hidNotLive
              cases hidNotLive
            rw [getElem?_setElem?_ne hNe hSet]
            exact hMatch.2 j hjLive
        · intro bbSrc' hBb'
          rw [hBb] at hBb'
          injection hBb' with hBbEq
          subst hBbEq
          refine ⟨hStmtLt, hTgtLe, ?_⟩
          have hStepDrop : bbSrc.statements.drop fSrc.stmtIdx = (.storageDead id) :: bbSrc.statements.drop (fSrc.stmtIdx + 1) :=
            drop_getElem?_succ bbSrc.statements fSrc.stmtIdx (.storageDead id) hStmt
          rw [hStepDrop] at hDropEq
          exact hDropEq

noncomputable def remapKeptStmt (smap : List Nat) : StatementKind → StatementKind
  | .assign dst rv => .assign (remapPlace smap dst) (remapRvalue smap rv)
  | _ => .unsupported

private theorem evalStatement_kept_compact {bSrc : Body} {spec : CompactionSpec}
    (hValid : ValidBodyCompaction bSrc spec)
    {fSrc fTgt : FrameState} {callerMem : CallerMemory}
    (hDef : fSrc.defId = fTgt.defId)
    (hBlk : fSrc.blockIdx = fTgt.blockIdx)
    (hMatch : LiveSlotsMatch spec.liveMask spec.slotMap fSrc.locals fTgt.locals)
    {stmtSrc : StatementKind}
    (hNotStutter : isStutterStmt stmtSrc = false)
    (hStmtRef : stmtRefLocalsInMask spec.liveMask stmtSrc = true) :
    match evalStatement bSrc fSrc callerMem stmtSrc,
        evalStatement (compactBody spec bSrc) fTgt callerMem (remapKeptStmt spec.slotMap stmtSrc) with
    | .fault k1, .fault k2 => k1 = k2
    | .done o1, .done o2 => o1 = o2
    | .step s1, .step s2 =>
      s1.callerMem = s2.callerMem ∧
      ∃ (f1 f2 : FrameState),
        s1.frames = [f1] ∧ s2.frames = [f2] ∧
        f1.defId = fSrc.defId ∧ f1.defId = f2.defId ∧
        f1.blockIdx = fSrc.blockIdx ∧ f1.blockIdx = f2.blockIdx ∧
        f1.stmtIdx = fSrc.stmtIdx + 1 ∧ f2.stmtIdx = fTgt.stmtIdx + 1 ∧
        LiveSlotsMatch spec.liveMask spec.slotMap f1.locals f2.locals
    | _, _ => False := by
  let ⟨_, hInj, hTy, _, _⟩ := hValid
  cases stmtSrc with
  | nop | storageLive _ | storageDead _ => cases hNotStutter
  | unsupported => rfl
  | assign dst rv =>
    change (isLiveLocal spec.liveMask dst.localId && rvalueLocalsInMask spec.liveMask rv) = true at hStmtRef
    cases hDstLive : isLiveLocal spec.liveMask dst.localId with
    | false =>
      rw [hDstLive] at hStmtRef
      cases hStmtRef
    | true =>
      rw [hDstLive] at hStmtRef
      unfold evalStatement compactBody remapKeptStmt remapPlace
      dsimp only
      cases !dst.projection.isEmpty with
      | true => rfl
      | false =>
        have hTyEq := (hTy.2.2.2.2 dst.localId hDstLive).2
        rw [hTyEq]
        cases hDstTy : Trusted.MirSemantics.getElem? bSrc.locals dst.localId with
        | none => rfl
        | some dstTy =>
          dsimp only
          have hRv := evalRvalue_compact hInj hTy hMatch dstTy hStmtRef
          cases hEvalSrc : evalRvalue bSrc.locals fSrc.locals dstTy rv with
          | error k1 =>
            cases hEvalTgt : evalRvalue spec.targetLocals fTgt.locals dstTy (remapRvalue spec.slotMap rv) with
            | error k2 =>
              rw [hEvalSrc, hEvalTgt] at hRv
              exact hRv
            | ok p2 =>
              rw [hEvalSrc, hEvalTgt] at hRv
              exact False.elim hRv
          | ok p1 =>
            cases hEvalTgt : evalRvalue spec.targetLocals fTgt.locals dstTy (remapRvalue spec.slotMap rv) with
            | error k2 =>
              rw [hEvalSrc, hEvalTgt] at hRv
              exact False.elim hRv
            | ok p2 =>
              rw [hEvalSrc, hEvalTgt] at hRv
              dsimp only at hRv; dsimp only
              let ⟨hvEq, hMatch1⟩ := hRv
              rw [← hvEq]
              have hWr := writePlace_compact hInj hMatch1 hDstLive dstTy p1.1
              cases hWrSrc : writePlace p1.2 dst.localId dstTy p1.1 with
              | error k1 =>
                cases hWrTgt : writePlace p2.2 (mapLocal spec.slotMap dst.localId) dstTy p1.1 with
                | error k2 =>
                  rw [hWrSrc, hWrTgt] at hWr
                  exact hWr
                | ok ls2 =>
                  rw [hWrSrc, hWrTgt] at hWr
                  exact False.elim hWr
              | ok ls1 =>
                cases hWrTgt : writePlace p2.2 (mapLocal spec.slotMap dst.localId) dstTy p1.1 with
                | error k2 =>
                  rw [hWrSrc, hWrTgt] at hWr
                  exact False.elim hWr
                | ok ls2 =>
                  rw [hWrSrc, hWrTgt] at hWr
                  exact ⟨rfl, _, _, rfl, rfl, rfl, hDef, rfl, hBlk, rfl, rfl, hWr⟩

private theorem evalTerminator_compact {bSrc : Body} {spec : CompactionSpec}
    (hValid : ValidBodyCompaction bSrc spec)
    {fSrc fTgt : FrameState} {callerMem : CallerMemory}
    (hDef : fSrc.defId = fTgt.defId)
    (hMatch : LiveSlotsMatch spec.liveMask spec.slotMap fSrc.locals fTgt.locals)
    (bbSrc : BasicBlock)
    (hTermRef : termLocalsInMask spec.liveMask bbSrc.terminator = true) :
    match evalTerminator bSrc bbSrc fSrc callerMem,
        evalTerminator (compactBody spec bSrc) (compactBasicBlock spec.slotMap bbSrc) fTgt callerMem with
    | .fault k1, .fault k2 => k1 = k2
    | .done o1, .done o2 => o1 = o2
    | .step s1, .step s2 =>
      s1.callerMem = s2.callerMem ∧
      ∃ (f1 f2 : FrameState),
        s1.frames = [f1] ∧ s2.frames = [f2] ∧
        f1.defId = fSrc.defId ∧ f1.defId = f2.defId ∧
        f1.blockIdx = f2.blockIdx ∧
        f1.stmtIdx = 0 ∧ f2.stmtIdx = 0 ∧
        LiveSlotsMatch spec.liveMask spec.slotMap f1.locals f2.locals
    | _, _ => False := by
  let ⟨hAbi, hInj, hTy, _, _⟩ := hValid
  cases hTerm : bbSrc.terminator with
  | goto target =>
    unfold evalTerminator compactBasicBlock remapTerminator jumpToBlock
    dsimp only
    rw [hTerm]
    exact ⟨rfl, _, _, rfl, rfl, rfl, hDef, rfl, rfl, rfl, hMatch⟩
  | return_ =>
    unfold evalTerminator compactBasicBlock remapTerminator
    dsimp only
    rw [hTerm]
    cases bbSrc.cleanup with
    | true => rfl
    | false =>
      dsimp only
      let ⟨h0Live, h0Map⟩ := hAbi.2 0 (Nat.zero_le _)
      have hSlot0 := hMatch.2 0 h0Live
      rw [h0Map] at hSlot0
      rw [hSlot0]
      cases hGet0 : Trusted.MirSemantics.getElem? fSrc.locals 0 with
      | none => rfl
      | some slot0 =>
        cases slot0 with
        | dead => rfl
        | live ov =>
          cases ov <;> rfl
  | unreachable =>
    unfold evalTerminator compactBasicBlock remapTerminator
    dsimp only
    rw [hTerm]
  | switchInt discr targets =>
    rw [hTerm] at hTermRef
    change operandLocalsInMask spec.liveMask discr = true at hTermRef
    unfold evalTerminator compactBasicBlock remapTerminator compactBody
    dsimp only
    rw [hTerm]
    dsimp only
    have hDiscr := evalPrimitiveOperand_compact hInj hTy hMatch hTermRef
    cases hSrc : evalPrimitiveOperand bSrc.locals fSrc.locals discr with
    | error k1 =>
      cases hTgt : evalPrimitiveOperand spec.targetLocals fTgt.locals (remapOperand spec.slotMap discr) with
      | error k2 =>
        rw [hSrc, hTgt] at hDiscr
        dsimp only at hDiscr
        exact hDiscr
      | ok p2 =>
        rw [hSrc, hTgt] at hDiscr
        exact False.elim hDiscr
    | ok p1 =>
      cases p1 with
      | mk v1 ls1 =>
        cases hTgt : evalPrimitiveOperand spec.targetLocals fTgt.locals (remapOperand spec.slotMap discr) with
        | error k2 =>
          rw [hSrc, hTgt] at hDiscr
          exact False.elim hDiscr
        | ok p2 =>
          cases p2 with
          | mk v2 ls2 =>
            rw [hSrc, hTgt] at hDiscr
            dsimp only at hDiscr; dsimp only
            let ⟨hvEq, hMatch1⟩ := hDiscr
            rw [← hvEq]
            cases v1 with
            | scalar sv =>
              dsimp only
              cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
              | error _ => rfl
              | ok tgt =>
                exact ⟨rfl, _, _, rfl, rfl, rfl, hDef, rfl, rfl, rfl, hMatch1⟩
            | bool b =>
              dsimp only
              cases evalBoolSwitchBranches b targets.otherwise targets.branches with
              | error _ => rfl
              | ok tgt =>
                exact ⟨rfl, _, _, rfl, rfl, rfl, hDef, rfl, rfl, rfl, hMatch1⟩
            | ptr _ | unit | tuple _ | bytes _ | enumVal _ _ => rfl
  | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | unsupported =>
    unfold evalTerminator compactBasicBlock remapTerminator
    dsimp only
    rw [hTerm]

private theorem evalStep_compact_cases {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {sSrc sTgt : State} (hRel : CompactedStateRel specs pSrc sSrc sTgt) :
    (∃ sSrc' stmt,
      isStutterStmt stmt = true ∧
      evalStep pSrc 0 sSrc = .step sSrc' ∧
      CompactedStateRel specs pSrc sSrc' sTgt ∧
      ∃ fSrc fSrc' bSrc bbSrc,
        sSrc.frames = [fSrc] ∧
        sSrc'.frames = [fSrc'] ∧
        Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc ∧
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc ∧
        Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx = some stmt ∧
        fSrc'.defId = fSrc.defId ∧
        fSrc'.blockIdx = fSrc.blockIdx ∧
        fSrc'.stmtIdx = fSrc.stmtIdx + 1) ∨
    (match evalStep pSrc 0 sSrc, evalStep (compactProgram specs pSrc) 0 sTgt with
     | .fault k1, .fault k2 => k1 = k2
     | .done o1, .done o2 => o1 = o2
     | .step s1, .step s2 => CompactedStateRel specs pSrc s1 s2
     | _, _ => False) := by
  let ⟨hMem, fSrc, fTgt, bSrc, spec, hFS, hFT, hDef, hBlk, hBSrc, hSpec, hMatch, hBlockInv⟩ := hRel
  have hBodySpec := getElem?_compactBodyList_some hBSrc hSpec
  have hBodyValid := hValid.2 fSrc.defId bSrc spec hBSrc hSpec
  let ⟨hAbi, hInj, hTy, hRef, hDead⟩ := hBodyValid
  cases hBbSrc : Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx with
  | none =>
    right
    unfold evalStep compactProgram
    dsimp only
    rw [hFS, hFT]
    dsimp only
    rw [← hDef, ← hBlk, hBSrc, hBodySpec]
    dsimp only [compactBody]
    rw [getElem?_compactBasicBlockList, hBbSrc]
  | some bbSrc =>
    let ⟨hSrcLe, hTgtLe, hDropEq⟩ := hBlockInv bbSrc hBbSrc
    cases hStmtSrc : Trusted.MirSemantics.getElem? bbSrc.statements fSrc.stmtIdx with
    | some stmt =>
      cases hStut : isStutterStmt stmt with
      | true =>
        left
        have hStepSrc : evalStep pSrc 0 sSrc = evalStatement bSrc fSrc sSrc.callerMem stmt := by
          unfold evalStep
          rw [hFS]; dsimp only
          rw [hBSrc]; dsimp only
          rw [hBbSrc]; dsimp only
          rw [hStmtSrc]
        let ⟨sSrc', hEval, hRel', fSrc', hFS', hDef', hBlk', hIdx'⟩ :=
          evalStatement_stutter_compact hValid hRel hFS hBSrc hSpec hBbSrc hStmtSrc hStut
        rw [hEval] at hStepSrc
        exact ⟨sSrc', stmt, hStut, hStepSrc, hRel', fSrc, fSrc', bSrc, bbSrc, hFS, hFS', hBSrc, hBbSrc, hStmtSrc, hDef', hBlk', hIdx'⟩
      | false =>
        right
        have hDropSrc : bbSrc.statements.drop fSrc.stmtIdx = stmt :: bbSrc.statements.drop (fSrc.stmtIdx + 1) :=
          drop_getElem?_succ bbSrc.statements fSrc.stmtIdx stmt hStmtSrc
        rw [hDropSrc] at hDropEq
        have hCompactCons : compactStatements spec.slotMap (stmt :: bbSrc.statements.drop (fSrc.stmtIdx + 1)) =
            remapKeptStmt spec.slotMap stmt :: compactStatements spec.slotMap (bbSrc.statements.drop (fSrc.stmtIdx + 1)) := by
          cases stmt with
          | nop | storageLive _ | storageDead _ => cases hStut
          | assign _ _ | unsupported => rfl
        rw [hCompactCons] at hDropEq
        let ⟨hStmtTgt, hTailDrop⟩ := drop_eq_cons_getElem? hDropEq.symm
        have hStmtRef := stmtRefLocalsInMask_of_pos hRef hBbSrc hStmtSrc
        have hKept := evalStatement_kept_compact hBodyValid (callerMem := sSrc.callerMem) hDef hBlk hMatch hStut hStmtRef
        have hSrcEval : evalStep pSrc 0 sSrc = evalStatement bSrc fSrc sSrc.callerMem stmt := by
          unfold evalStep
          rw [hFS]; dsimp only
          rw [hBSrc]; dsimp only
          rw [hBbSrc]; dsimp only
          rw [hStmtSrc]
        have hTgtEval : evalStep (compactProgram specs pSrc) 0 sTgt =
            evalStatement (compactBody spec bSrc) fTgt sSrc.callerMem (remapKeptStmt spec.slotMap stmt) := by
          unfold evalStep compactProgram
          dsimp only
          rw [hFT]; dsimp only
          rw [← hMem, ← hDef, ← hBlk, hBodySpec]; dsimp only [compactBody]
          rw [getElem?_compactBasicBlockList, hBbSrc]; dsimp only
          rw [hStmtTgt]
        rw [hSrcEval, hTgtEval]
        cases hS1 : evalStatement bSrc fSrc sSrc.callerMem stmt with
        | fault k1 =>
          rw [hS1] at hKept
          cases hS2 : evalStatement (compactBody spec bSrc) fTgt sSrc.callerMem (remapKeptStmt spec.slotMap stmt) with
          | fault k2 => rw [hS2] at hKept; exact hKept
          | done o2 => rw [hS2] at hKept; exact False.elim hKept
          | step st2 => rw [hS2] at hKept; exact False.elim hKept
        | done o1 =>
          rw [hS1] at hKept
          cases hS2 : evalStatement (compactBody spec bSrc) fTgt sSrc.callerMem (remapKeptStmt spec.slotMap stmt) with
          | fault k2 => rw [hS2] at hKept; exact False.elim hKept
          | done o2 => rw [hS2] at hKept; exact hKept
          | step st2 => rw [hS2] at hKept; exact False.elim hKept
        | step st1 =>
          rw [hS1] at hKept
          cases hS2 : evalStatement (compactBody spec bSrc) fTgt sSrc.callerMem (remapKeptStmt spec.slotMap stmt) with
          | fault k2 => rw [hS2] at hKept; exact False.elim hKept
          | done o2 => rw [hS2] at hKept; exact False.elim hKept
          | step st2 =>
            rw [hS2] at hKept
            let ⟨hMem', f1, f2, hF1, hF2, hDef1Src, hDef1, hBlk1Src, hBlk1, hIdx1, hIdx2, hMatch'⟩ := hKept
            refine ⟨hMem', f1, f2, bSrc, spec, hF1, hF2, hDef1, hBlk1, ?_, ?_, hMatch', ?_⟩
            · rw [hDef1Src]; exact hBSrc
            · rw [hDef1Src]; exact hSpec
            · intro bbSrc' hBb'
              rw [hBlk1Src, hBbSrc] at hBb'
              injection hBb' with hBbEq
              subst hBbEq
              have hTgtLt : fTgt.stmtIdx < (compactBasicBlock spec.slotMap bbSrc).statements.length :=
                getElem?_eq_some_lt hStmtTgt
              rw [hIdx1, hIdx2]
              exact ⟨getElem?_eq_some_lt hStmtSrc, hTgtLt, hTailDrop.symm⟩
    | none =>
      right
      have hSrcIdxEq : fSrc.stmtIdx = bbSrc.statements.length := by
        cases Nat.lt_or_ge fSrc.stmtIdx bbSrc.statements.length with
        | inl hLt =>
          let ⟨_, hSome⟩ := getElem?_lt_some bbSrc.statements hLt
          rw [hStmtSrc] at hSome
          cases hSome
        | inr hGe =>
          exact Nat.le_antisymm hSrcLe hGe
      have hSrcNil : bbSrc.statements.drop fSrc.stmtIdx = [] := by
        rw [hSrcIdxEq]
        exact drop_length_eq_nil bbSrc.statements
      rw [hSrcNil] at hDropEq
      have hTgtNil : (compactBasicBlock spec.slotMap bbSrc).statements.drop fTgt.stmtIdx = [] :=
        hDropEq.symm
      have hTgtIdxEq : fTgt.stmtIdx = (compactBasicBlock spec.slotMap bbSrc).statements.length :=
        (drop_eq_nil_iff _ fTgt.stmtIdx hTgtLe).mp hTgtNil
      have hTermRef := termLocalsInMask_of_pos hRef hBbSrc
      have hTerm := evalTerminator_compact hBodyValid (callerMem := sSrc.callerMem) hDef hMatch bbSrc hTermRef
      have hTgtNone : Trusted.MirSemantics.getElem? (compactBasicBlock spec.slotMap bbSrc).statements fTgt.stmtIdx = none :=
        getElem?_none_iff.mpr (by rw [hTgtIdxEq]; exact Nat.le_refl _)
      have hSrcEval : evalStep pSrc 0 sSrc = evalTerminator bSrc bbSrc fSrc sSrc.callerMem := by
        unfold evalStep
        rw [hFS]; dsimp only
        rw [hBSrc]; dsimp only
        rw [hBbSrc]; dsimp only
        rw [hStmtSrc]; dsimp only
        rw [bool_ite_pos (by rw [hSrcIdxEq]; exact nat_beq_refl _)]
      have hTgtEval : evalStep (compactProgram specs pSrc) 0 sTgt =
          evalTerminator (compactBody spec bSrc) (compactBasicBlock spec.slotMap bbSrc) fTgt sSrc.callerMem := by
        unfold evalStep compactProgram
        dsimp only
        rw [hFT]; dsimp only
        rw [← hMem, ← hDef, ← hBlk, hBodySpec]; dsimp only [compactBody]
        rw [getElem?_compactBasicBlockList, hBbSrc]; dsimp only
        rw [hTgtNone]; dsimp only
        rw [bool_ite_pos (by rw [hTgtIdxEq]; exact nat_beq_refl _)]
      rw [hSrcEval, hTgtEval]
      cases hT1 : evalTerminator bSrc bbSrc fSrc sSrc.callerMem with
      | fault k1 =>
        rw [hT1] at hTerm
        cases hT2 : evalTerminator (compactBody spec bSrc) (compactBasicBlock spec.slotMap bbSrc) fTgt sSrc.callerMem with
        | fault k2 => rw [hT2] at hTerm; exact hTerm
        | done o2 => rw [hT2] at hTerm; exact False.elim hTerm
        | step st2 => rw [hT2] at hTerm; exact False.elim hTerm
      | done o1 =>
        rw [hT1] at hTerm
        cases hT2 : evalTerminator (compactBody spec bSrc) (compactBasicBlock spec.slotMap bbSrc) fTgt sSrc.callerMem with
        | fault k2 => rw [hT2] at hTerm; exact False.elim hTerm
        | done o2 => rw [hT2] at hTerm; exact hTerm
        | step st2 => rw [hT2] at hTerm; exact False.elim hTerm
      | step st1 =>
        rw [hT1] at hTerm
        cases hT2 : evalTerminator (compactBody spec bSrc) (compactBasicBlock spec.slotMap bbSrc) fTgt sSrc.callerMem with
        | fault k2 => rw [hT2] at hTerm; exact False.elim hTerm
        | done o2 => rw [hT2] at hTerm; exact False.elim hTerm
        | step st2 =>
          rw [hT2] at hTerm
          let ⟨hMem', f1, f2, hF1, hF2, hDef1Src, hDef1, hBlk1, hIdx1, hIdx2, hMatch'⟩ := hTerm
          refine ⟨hMem', f1, f2, bSrc, spec, hF1, hF2, hDef1, hBlk1, ?_, ?_, hMatch', ?_⟩
          · rw [hDef1Src]; exact hBSrc
          · rw [hDef1Src]; exact hSpec
          · intro bbSrc' _
            rw [hIdx1, hIdx2]
            exact ⟨Nat.zero_le _, Nat.zero_le _, rfl⟩

private theorem reaches_trans {p : Program} {s1 s2 s3 : State}
    (h12 : Reaches p s1 s2) (h23 : Reaches p s2 s3) :
    Reaches p s1 s3 := by
  induction h23 with
  | refl => exact h12
  | tail _ hStep ih => exact Reaches.tail ih hStep

private theorem src_flush_frontier {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) :
    ∀ (k : Nat) {sSrc sTgt : State},
      CompactedStateRel specs pSrc sSrc sTgt →
      (∀ fSrc bSrc bbSrc,
        sSrc.frames = [fSrc] →
        Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
        bbSrc.statements.length - fSrc.stmtIdx ≤ k) →
      ∃ sFrontier : State,
        Reaches pSrc sSrc sFrontier ∧
        CompactedStateRel specs pSrc sFrontier sTgt ∧
        (match evalStep pSrc 0 sFrontier, evalStep (compactProgram specs pSrc) 0 sTgt with
         | .fault k1, .fault k2 => k1 = k2
         | .done o1, .done o2 => o1 = o2
         | .step s1, .step s2 => CompactedStateRel specs pSrc s1 s2
         | _, _ => False)
  | 0, sSrc, sTgt, hRel, hkBound => by
    cases evalStep_compact_cases hValid hRel with
    | inr hMatch => exact ⟨sSrc, Reaches.refl sSrc, hRel, hMatch⟩
    | inl hStut =>
      let ⟨_, _, _, _, _, fSrc, _, bSrc, bbSrc, hFS, _, hBS, hBb, hStmt, _, _, _⟩ := hStut
      have hLt := getElem?_eq_some_lt hStmt
      have hZero := hkBound fSrc bSrc bbSrc hFS hBS hBb
      have hSubZero : bbSrc.statements.length - fSrc.stmtIdx = 0 := Nat.le_zero.mp hZero
      have hGe : bbSrc.statements.length ≤ fSrc.stmtIdx := Nat.le_of_sub_eq_zero hSubZero
      exact False.elim (Nat.not_lt_of_ge hGe hLt)
  | k + 1, sSrc, sTgt, hRel, hkBound => by
    cases evalStep_compact_cases hValid hRel with
    | inr hMatch => exact ⟨sSrc, Reaches.refl sSrc, hRel, hMatch⟩
    | inl hStut =>
      let ⟨sSrc', _, _, hStep, hRel', fSrc, fSrc', bSrc, bbSrc, hFS, hFS', hBS, hBb, hStmt, hDef', hBlk', hIdx'⟩ := hStut
      have hBound' : ∀ fS bS bbS,
          sSrc'.frames = [fS] →
          Trusted.MirSemantics.getElem? pSrc.bodies fS.defId = some bS →
          Trusted.MirSemantics.getElem? bS.basicBlocks fS.blockIdx = some bbS →
          bbS.statements.length - fS.stmtIdx ≤ k := by
        intro fS bS bbS hF hB hBlock
        rw [hFS'] at hF
        injection hF with hFEq
        subst hFEq
        rw [hDef', hBS] at hB
        injection hB with hBEq
        subst hBEq
        rw [hBlk', hBb] at hBlock
        injection hBlock with hBbEq
        subst hBbEq
        have hPrev := hkBound fSrc bSrc bbSrc hFS hBS hBb
        have hLt : fSrc.stmtIdx < bbSrc.statements.length := getElem?_eq_some_lt hStmt
        rw [hIdx']
        -- direct Nat arithmetic without omega
        cases hRem : bbSrc.statements.length - fSrc.stmtIdx with
        | zero =>
          exact False.elim (Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero hRem) hLt)
        | succ m =>
          have hmLe : m ≤ k := by
            rw [hRem] at hPrev
            exact Nat.le_of_succ_le_succ hPrev
          have hSubEq : bbSrc.statements.length - (fSrc.stmtIdx + 1) = m := by
            rw [Nat.sub_succ, hRem]
            rfl
          rw [hSubEq]
          exact hmLe
      let ⟨sFrontier, hReach', hRelF, hMatchF⟩ := src_flush_frontier hValid k hRel' hBound'
      have hOne : Reaches pSrc sSrc sSrc' :=
        Reaches.tail (Reaches.refl sSrc) ⟨0, rfl, hStep⟩
      refine ⟨sFrontier, reaches_trans hOne hReach', hRelF, hMatchF⟩

private theorem step_det_eq {p : Program} {s : State} {r1 r2 : StepResult State TerminalOut}
    (h1 : Step p s r1) (h2 : Step p s r2) : r1 = r2 := by
  let ⟨c1, hc1, he1⟩ := h1
  let ⟨c2, hc2, he2⟩ := h2
  change c1 = 0 at hc1
  change c2 = 0 at hc2
  subst hc1; subst hc2
  rw [← he1, ← he2]

private theorem reaches_forward_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {sSrc0 sTgt0 : State} (hRel0 : CompactedStateRel specs pSrc sSrc0 sTgt0)
    {sSrc : State} (hReach : Reaches pSrc sSrc0 sSrc) :
    ∃ sTgt : State,
      Reaches (compactProgram specs pSrc) sTgt0 sTgt ∧
      CompactedStateRel specs pSrc sSrc sTgt := by
  induction hReach with
  | refl => exact ⟨sTgt0, Reaches.refl sTgt0, hRel0⟩
  | tail _ hStep ih =>
    let ⟨sTgt, hReachTgt, hRel⟩ := ih
    let ⟨c, hc, hEval⟩ := hStep
    change c = 0 at hc
    subst hc
    cases evalStep_compact_cases hValid hRel with
    | inl hStut =>
      let ⟨sSrc', _, _, hEvalStut, hRel', _⟩ := hStut
      rw [hEval] at hEvalStut
      injection hEvalStut with hEq
      rw [← hEq] at hRel'
      exact ⟨sTgt, hReachTgt, hRel'⟩
    | inr hSync =>
      rw [hEval] at hSync
      cases hTgtStep : evalStep (compactProgram specs pSrc) 0 sTgt with
      | fault k2 => rw [hTgtStep] at hSync; exact False.elim hSync
      | done o2 => rw [hTgtStep] at hSync; exact False.elim hSync
      | step sTgt' =>
        rw [hTgtStep] at hSync
        exact ⟨sTgt', Reaches.tail hReachTgt ⟨0, rfl, hTgtStep⟩, hSync⟩

private theorem reaches_backward_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {sSrc0 sTgt0 : State} (hRel0 : CompactedStateRel specs pSrc sSrc0 sTgt0)
    {sTgt : State} (hReach : Reaches (compactProgram specs pSrc) sTgt0 sTgt) :
    ∃ sSrc : State,
      Reaches pSrc sSrc0 sSrc ∧
      CompactedStateRel specs pSrc sSrc sTgt := by
  induction hReach with
  | refl => exact ⟨sSrc0, Reaches.refl sSrc0, hRel0⟩
  | tail _ hStep ih =>
    let ⟨sSrc, hReachSrc, hRel⟩ := ih
    let ⟨c, hc, hEvalTgt⟩ := hStep
    change c = 0 at hc
    subst hc
    let ⟨_, fS, _, bS, _, hFS, _, _, _, hBS, _, _, _⟩ := hRel
    have hExistK : ∃ k : Nat, ∀ fSrc bSrc bbSrc,
        sSrc.frames = [fSrc] →
        Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
        bbSrc.statements.length - fSrc.stmtIdx ≤ k := by
      cases hBb : Trusted.MirSemantics.getElem? bS.basicBlocks fS.blockIdx with
      | none =>
        refine ⟨0, fun f1 b1 bb1 hF1 hB1 hBb1 => ?_⟩
        rw [hFS] at hF1; injection hF1 with hFEq; subst hFEq
        rw [hBS] at hB1; injection hB1 with hBEq; subst hBEq
        rw [hBb] at hBb1; cases hBb1
      | some bbS =>
        refine ⟨bbS.statements.length - fS.stmtIdx, fun f1 b1 bb1 hF1 hB1 hBb1 => ?_⟩
        rw [hFS] at hF1; injection hF1 with hFEq; subst hFEq
        rw [hBS] at hB1; injection hB1 with hBEq; subst hBEq
        rw [hBb] at hBb1; injection hBb1 with hBbEq; subst hBbEq
        exact Nat.le_refl _
    let ⟨k, hkBound⟩ := hExistK
    let ⟨sFrontier, hFlush, _, hMatchF⟩ := src_flush_frontier hValid k hRel hkBound
    rw [hEvalTgt] at hMatchF
    cases hStepF : evalStep pSrc 0 sFrontier with
    | fault k1 => rw [hStepF] at hMatchF; exact False.elim hMatchF
    | done o1 => rw [hStepF] at hMatchF; exact False.elim hMatchF
    | step sSrc' =>
      rw [hStepF] at hMatchF
      have hReachFull : Reaches pSrc sSrc0 sSrc' :=
        Reaches.tail (reaches_trans hReachSrc hFlush) ⟨0, rfl, hStepF⟩
      exact ⟨sSrc', hReachFull, hMatchF⟩

private theorem reachesResult_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query)
    (res : StepResult State TerminalOut) :
    match res with
    | .done out => ReachesResult pSrc q (.done out) ↔ ReachesResult (compactProgram specs pSrc) q (.done out)
    | .fault k => ReachesResult pSrc q (.fault k) ↔ ReachesResult (compactProgram specs pSrc) q (.fault k)
    | .step _ => True := by
  have hInit := initState_compact_equiv hValid q
  cases res with
  | step _ => exact True.intro
  | done out =>
    unfold ReachesResult
    cases hSrc : initState pSrc q with
    | error k1 =>
      rw [hSrc] at hInit
      cases hTgt : initState (compactProgram specs pSrc) q with
      | error k2 =>
        rw [hTgt] at hInit
        constructor <;> intro h <;> cases h
      | ok _ => rw [hTgt] at hInit; exact False.elim hInit
    | ok sSrc0 =>
      rw [hSrc] at hInit
      cases hTgt : initState (compactProgram specs pSrc) q with
      | error _ => rw [hTgt] at hInit; exact False.elim hInit
      | ok sTgt0 =>
        rw [hTgt] at hInit
        constructor
        · intro ⟨sSrc, hReach, hStep⟩
          let ⟨sTgt, hReachTgt, hRel⟩ := reaches_forward_compact hValid hInit hReach
          let ⟨c, hc, hEval⟩ := hStep
          change c = 0 at hc; subst hc
          cases evalStep_compact_cases hValid hRel with
          | inl hStut =>
            let ⟨_, _, _, hS, _⟩ := hStut
            rw [hS] at hEval; cases hEval
          | inr hSync =>
            rw [hEval] at hSync
            cases hT : evalStep (compactProgram specs pSrc) 0 sTgt with
            | fault _ => rw [hT] at hSync; exact False.elim hSync
            | step _ => rw [hT] at hSync; exact False.elim hSync
            | done out2 =>
              rw [hT] at hSync
              subst hSync
              exact ⟨sTgt, hReachTgt, ⟨0, rfl, hT⟩⟩
        · intro ⟨sTgt, hReachTgt, hStepTgt⟩
          let ⟨sSrc, hReachSrc, hRel⟩ := reaches_backward_compact hValid hInit hReachTgt
          let ⟨c, hc, hEvalTgt⟩ := hStepTgt
          change c = 0 at hc; subst hc
          have hExistK : ∃ k : Nat, ∀ fSrc bSrc bbSrc,
              sSrc.frames = [fSrc] →
              Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
              Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
              bbSrc.statements.length - fSrc.stmtIdx ≤ k := by
            let ⟨_, fS, _, bS, _, hFS, _, _, _, hBS, _, _, _⟩ := hRel
            cases hBb : Trusted.MirSemantics.getElem? bS.basicBlocks fS.blockIdx with
            | none =>
              refine ⟨0, fun f1 b1 bb1 hF1 hB1 hBb1 => ?_⟩
              rw [hFS] at hF1; injection hF1 with hFEq; subst hFEq
              rw [hBS] at hB1; injection hB1 with hBEq; subst hBEq
              rw [hBb] at hBb1; cases hBb1
            | some bbS =>
              refine ⟨bbS.statements.length - fS.stmtIdx, fun f1 b1 bb1 hF1 hB1 hBb1 => ?_⟩
              rw [hFS] at hF1; injection hF1 with hFEq; subst hFEq
              rw [hBS] at hB1; injection hB1 with hBEq; subst hBEq
              rw [hBb] at hBb1; injection hBb1 with hBbEq; subst hBbEq
              exact Nat.le_refl _
          let ⟨k, hkBound⟩ := hExistK
          let ⟨sFrontier, hFlush, _, hMatchF⟩ := src_flush_frontier hValid k hRel hkBound
          rw [hEvalTgt] at hMatchF
          cases hF : evalStep pSrc 0 sFrontier with
          | fault _ => rw [hF] at hMatchF; exact False.elim hMatchF
          | step _ => rw [hF] at hMatchF; exact False.elim hMatchF
          | done out1 =>
            rw [hF] at hMatchF
            subst hMatchF
            exact ⟨sFrontier, reaches_trans hReachSrc hFlush, ⟨0, rfl, hF⟩⟩
  | fault k =>
    unfold ReachesResult
    cases hSrc : initState pSrc q with
    | error k1 =>
      rw [hSrc] at hInit
      cases hTgt : initState (compactProgram specs pSrc) q with
      | error k2 =>
        rw [hTgt] at hInit
        subst hInit
        exact Iff.rfl
      | ok _ => rw [hTgt] at hInit; exact False.elim hInit
    | ok sSrc0 =>
      rw [hSrc] at hInit
      cases hTgt : initState (compactProgram specs pSrc) q with
      | error _ => rw [hTgt] at hInit; exact False.elim hInit
      | ok sTgt0 =>
        rw [hTgt] at hInit
        constructor
        · intro ⟨sSrc, hReach, hStep⟩
          let ⟨sTgt, hReachTgt, hRel⟩ := reaches_forward_compact hValid hInit hReach
          let ⟨c, hc, hEval⟩ := hStep
          change c = 0 at hc; subst hc
          cases evalStep_compact_cases hValid hRel with
          | inl hStut =>
            let ⟨_, _, _, hS, _⟩ := hStut
            rw [hS] at hEval; cases hEval
          | inr hSync =>
            rw [hEval] at hSync
            cases hT : evalStep (compactProgram specs pSrc) 0 sTgt with
            | done _ => rw [hT] at hSync; exact False.elim hSync
            | step _ => rw [hT] at hSync; exact False.elim hSync
            | fault k2 =>
              rw [hT] at hSync
              subst hSync
              exact ⟨sTgt, hReachTgt, ⟨0, rfl, hT⟩⟩
        · intro ⟨sTgt, hReachTgt, hStepTgt⟩
          let ⟨sSrc, hReachSrc, hRel⟩ := reaches_backward_compact hValid hInit hReachTgt
          let ⟨c, hc, hEvalTgt⟩ := hStepTgt
          change c = 0 at hc; subst hc
          have hExistK : ∃ k0 : Nat, ∀ fSrc bSrc bbSrc,
              sSrc.frames = [fSrc] →
              Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
              Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
              bbSrc.statements.length - fSrc.stmtIdx ≤ k0 := by
            let ⟨_, fS, _, bS, _, hFS, _, _, _, hBS, _, _, _⟩ := hRel
            cases hBb : Trusted.MirSemantics.getElem? bS.basicBlocks fS.blockIdx with
            | none =>
              refine ⟨0, fun f1 b1 bb1 hF1 hB1 hBb1 => ?_⟩
              rw [hFS] at hF1; injection hF1 with hFEq; subst hFEq
              rw [hBS] at hB1; injection hB1 with hBEq; subst hBEq
              rw [hBb] at hBb1; cases hBb1
            | some bbS =>
              refine ⟨bbS.statements.length - fS.stmtIdx, fun f1 b1 bb1 hF1 hB1 hBb1 => ?_⟩
              rw [hFS] at hF1; injection hF1 with hFEq; subst hFEq
              rw [hBS] at hB1; injection hB1 with hBEq; subst hBEq
              rw [hBb] at hBb1; injection hBb1 with hBbEq; subst hBbEq
              exact Nat.le_refl _
          let ⟨k0, hkBound⟩ := hExistK
          let ⟨sFrontier, hFlush, _, hMatchF⟩ := src_flush_frontier hValid k0 hRel hkBound
          rw [hEvalTgt] at hMatchF
          cases hF : evalStep pSrc 0 sFrontier with
          | done _ => rw [hF] at hMatchF; exact False.elim hMatchF
          | step _ => rw [hF] at hMatchF; exact False.elim hMatchF
          | fault k1 =>
            rw [hF] at hMatchF
            subst hMatchF
            exact ⟨sFrontier, reaches_trans hReachSrc hFlush, ⟨0, rfl, hF⟩⟩

theorem wellFormed_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query) :
    WellFormed pSrc q ↔ WellFormed (compactProgram specs pSrc) q := by
  have hInit := initState_compact_equiv hValid q
  have hFaultIff : ∀ k : FaultKind,
      ReachesResult pSrc q (.fault k) ↔ ReachesResult (compactProgram specs pSrc) q (.fault k) :=
    fun k => reachesResult_compact_iff hValid q (.fault k)
  unfold WellFormed
  cases hSrc : initState pSrc q with
  | error k1 =>
    rw [hSrc] at hInit
    cases hTgt : initState (compactProgram specs pSrc) q with
    | error _ =>
      rw [hTgt] at hInit
      constructor <;> intro ⟨⟨s0, hEq, _⟩, _⟩ <;> cases hEq
    | ok _ => rw [hTgt] at hInit; exact False.elim hInit
  | ok sSrc0 =>
    rw [hSrc] at hInit
    cases hTgt : initState (compactProgram specs pSrc) q with
    | error _ => rw [hTgt] at hInit; exact False.elim hInit
    | ok sTgt0 =>
      rw [hTgt] at hInit
      constructor
      · intro ⟨_, hNoFault⟩
        refine ⟨⟨sTgt0, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hk => hNoFault k ((hFaultIff k).mpr hk)⟩
      · intro ⟨_, hNoFault⟩
        refine ⟨⟨sSrc0, rfl, fun _ _ => ⟨0, rfl⟩⟩, fun k hk => hNoFault k ((hFaultIff k).mp hk)⟩

theorem behavior_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query) (out : TerminalOut) :
    Behavior pSrc q out ↔ Behavior (compactProgram specs pSrc) q out :=
  reachesResult_compact_iff hValid q (.done out)

/-- Constructive one-step deterministic transition function (`Classical.choice`-free). -/
noncomputable def iterNextState (p : Program) (s : State) : State :=
  match evalStep p 0 s with
  | .step s' => s'
  | .done _ => s
  | .fault _ => s

/-- Constructive deterministic trace generator from initial state `s0`. -/
noncomputable def iterTrace (p : Program) (s0 : State) : Nat → State
  | 0 => s0
  | n + 1 => iterNextState p (iterTrace p s0 n)

private theorem reaches_along_trace {p : Program} {s0 : State}
    (trace : Nat → State) (h0 : trace 0 = s0)
    (hStep : ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))) :
    ∀ {s : State}, Reaches p s0 s → ∃ n : Nat, s = trace n := by
  intro s hReach
  induction hReach with
  | refl => exact ⟨0, h0.symm⟩
  | tail _ hS ih =>
    let ⟨n, hn⟩ := ih
    subst hn
    have hEq := step_det_eq hS (hStep n)
    injection hEq with hStateEq
    exact ⟨n + 1, hStateEq⟩

private theorem diverges_not_reachesResult_done {p : Program} {q : Query}
    (hDiv : Diverges p q) (out : TerminalOut) :
    ¬ ReachesResult p q (.done out) := by
  let ⟨s0, hInit, trace, h0, hStep⟩ := hDiv
  intro hRes
  unfold ReachesResult at hRes
  rw [hInit] at hRes
  let ⟨s, hReach, hDone⟩ := hRes
  let ⟨n, hn⟩ := reaches_along_trace trace h0 hStep hReach
  subst hn
  have hContra := step_det_eq (hStep n) hDone
  cases hContra

private theorem diverges_not_reachesResult_fault {p : Program} {q : Query}
    (hDiv : Diverges p q) (k : FaultKind) :
    ¬ ReachesResult p q (.fault k) := by
  let ⟨s0, hInit, trace, h0, hStep⟩ := hDiv
  intro hRes
  unfold ReachesResult at hRes
  rw [hInit] at hRes
  let ⟨s, hReach, hFault⟩ := hRes
  let ⟨n, hn⟩ := reaches_along_trace trace h0 hStep hReach
  subst hn
  have hContra := step_det_eq (hStep n) hFault
  cases hContra

private theorem iterTrace_diverges_of_no_halt {p : Program} {q : Query} {s0 : State}
    (hInit : initState p q = .ok s0)
    (hNoDone : ∀ out : TerminalOut, ¬ ReachesResult p q (.done out))
    (hNoFault : ∀ k : FaultKind, ¬ ReachesResult p q (.fault k)) :
    Diverges p q := by
  have hInv : ∀ n : Nat,
      Reaches p s0 (iterTrace p s0 n) ∧
      Step p (iterTrace p s0 n) (.step (iterTrace p s0 (n + 1))) := by
    intro n
    induction n with
    | zero =>
      change Reaches p s0 s0 ∧ Step p s0 (.step (iterNextState p s0))
      refine ⟨Reaches.refl s0, ?_⟩
      cases hEv : evalStep p 0 s0 with
      | step s1 =>
        unfold iterNextState
        rw [hEv]
        exact ⟨0, rfl, hEv⟩
      | done out =>
        have hBad : ReachesResult p q (.done out) := by
          unfold ReachesResult
          rw [hInit]
          exact ⟨s0, Reaches.refl s0, ⟨0, rfl, hEv⟩⟩
        exact False.elim (hNoDone out hBad)
      | fault k =>
        have hBad : ReachesResult p q (.fault k) := by
          unfold ReachesResult
          rw [hInit]
          exact ⟨s0, Reaches.refl s0, ⟨0, rfl, hEv⟩⟩
        exact False.elim (hNoFault k hBad)
    | succ m ih =>
      let ⟨hReachM, hStepM⟩ := ih
      have hReachSucc : Reaches p s0 (iterTrace p s0 (m + 1)) :=
        Reaches.tail hReachM hStepM
      refine ⟨hReachSucc, ?_⟩
      cases hEv : evalStep p 0 (iterTrace p s0 (m + 1)) with
      | step sNext =>
        change Step p (iterTrace p s0 (m + 1)) (.step (iterNextState p (iterTrace p s0 (m + 1))))
        unfold iterNextState
        rw [hEv]
        exact ⟨0, rfl, hEv⟩
      | done out =>
        have hBad : ReachesResult p q (.done out) := by
          unfold ReachesResult
          rw [hInit]
          exact ⟨iterTrace p s0 (m + 1), hReachSucc, ⟨0, rfl, hEv⟩⟩
        exact False.elim (hNoDone out hBad)
      | fault k =>
        have hBad : ReachesResult p q (.fault k) := by
          unfold ReachesResult
          rw [hInit]
          exact ⟨iterTrace p s0 (m + 1), hReachSucc, ⟨0, rfl, hEv⟩⟩
        exact False.elim (hNoFault k hBad)
  exact ⟨s0, hInit, iterTrace p s0, rfl, fun n => (hInv n).2⟩

/-- Constructive bidirectional preservation of `Diverges` (zero `Classical.choice`). -/
theorem diverges_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query) :
    Diverges pSrc q ↔ Diverges (compactProgram specs pSrc) q := by
  have hInit := initState_compact_equiv hValid q
  have hDoneIff : ∀ out : TerminalOut,
      ReachesResult pSrc q (.done out) ↔ ReachesResult (compactProgram specs pSrc) q (.done out) :=
    fun out => reachesResult_compact_iff hValid q (.done out)
  have hFaultIff : ∀ k : FaultKind,
      ReachesResult pSrc q (.fault k) ↔ ReachesResult (compactProgram specs pSrc) q (.fault k) :=
    fun k => reachesResult_compact_iff hValid q (.fault k)
  constructor
  · intro hDivSrc
    cases hSrcInit : initState pSrc q with
    | error _ =>
      let ⟨s0, h0, _⟩ := hDivSrc
      rw [hSrcInit] at h0; cases h0
    | ok sSrc0 =>
      rw [hSrcInit] at hInit
      cases hTgtInit : initState (compactProgram specs pSrc) q with
      | error _ => rw [hTgtInit] at hInit; exact False.elim hInit
      | ok sTgt0 =>
        exact iterTrace_diverges_of_no_halt hTgtInit
          (fun out hRes => diverges_not_reachesResult_done hDivSrc out ((hDoneIff out).mpr hRes))
          (fun k hRes => diverges_not_reachesResult_fault hDivSrc k ((hFaultIff k).mpr hRes))
  · intro hDivTgt
    cases hTgtInit : initState (compactProgram specs pSrc) q with
    | error _ =>
      let ⟨s0, h0, _⟩ := hDivTgt
      rw [hTgtInit] at h0; cases h0
    | ok sTgt0 =>
      rw [hTgtInit] at hInit
      cases hSrcInit : initState pSrc q with
      | error _ => rw [hSrcInit] at hInit; exact False.elim hInit
      | ok sSrc0 =>
        exact iterTrace_diverges_of_no_halt hSrcInit
          (fun out hRes => diverges_not_reachesResult_done hDivTgt out ((hDoneIff out).mp hRes))
          (fun k hRes => diverges_not_reachesResult_fault hDivTgt k ((hFaultIff k).mp hRes))

theorem satisfiesPost_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query)
    (post : TerminalOut → Prop) :
    SatisfiesPost pSrc q post ↔ SatisfiesPost (compactProgram specs pSrc) q post := by
  unfold SatisfiesPost
  have hWf := wellFormed_compact_iff hValid q
  constructor
  · intro ⟨hW, hPost⟩
    exact ⟨hWf.mp hW, fun out hB => hPost out ((behavior_compact_iff hValid q out).mpr hB)⟩
  · intro ⟨hW, hPost⟩
    exact ⟨hWf.mpr hW, fun out hB => hPost out ((behavior_compact_iff hValid q out).mp hB)⟩

/-- Unified top-level bidirectional operational equivalence for `R0 -> R3` compaction. -/
theorem compact_preserves_eval_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc) (q : Query)
    (post : TerminalOut → Prop) :
    (WellFormed pSrc q ↔ WellFormed (compactProgram specs pSrc) q) ∧
    (∀ out, Behavior pSrc q out ↔ Behavior (compactProgram specs pSrc) q out) ∧
    (∀ k, ReachesResult pSrc q (.fault k) ↔ ReachesResult (compactProgram specs pSrc) q (.fault k)) ∧
    (Diverges pSrc q ↔ Diverges (compactProgram specs pSrc) q) ∧
    (SatisfiesPost pSrc q post ↔ SatisfiesPost (compactProgram specs pSrc) q post) :=
  ⟨wellFormed_compact_iff hValid q,
   fun out => behavior_compact_iff hValid q out,
   fun k => reachesResult_compact_iff hValid q (.fault k),
   diverges_compact_iff hValid q,
   satisfiesPost_compact_iff hValid q post⟩

private theorem bodyStaticAdmitted_compact {pSrc : Program} {bSrc : Body} {spec : CompactionSpec}
    (hValid : ValidBodyCompaction bSrc spec) :
    BodyStaticAdmitted (compactProgram specs pSrc) (compactBody spec bSrc) =
      BodyStaticAdmitted pSrc bSrc := by
  let ⟨hAbi, _, hTy, _, hDead⟩ := hValid
  unfold BodyStaticAdmitted compactProgram
  dsimp only
  have hAnnTgt := storageAnnotationsInBounds_compactBody spec bSrc
  rw [hAnnTgt]
  dsimp only [compactBody]
  have hEmpty := compactBasicBlockList_isEmpty spec.slotMap bSrc.basicBlocks
  have hArgSrc : Nat.blt bSrc.argumentCount bSrc.locals.length = true := by
    apply nat_blt_true_iff.mpr
    rw [← hTy.1]
    exact hAbi.1
  have hArgTgt : Nat.blt bSrc.argumentCount spec.targetLocals.length = true :=
    nat_blt_true_iff.mpr hTy.2.1
  have hAnnSrc := storageAnnotationsInBounds_src_of_dead hDead
  rw [hEmpty, hArgSrc, hArgTgt, hAnnSrc, hTy.2.2.1, hTy.2.2.2.1]

private theorem validEntryArgs_compact_iff {bSrc : Body} {spec : CompactionSpec}
    (hAbi : PreservesAbiSlots bSrc.argumentCount spec)
    (hTy : ValidTargetTypes bSrc spec) (args : List Val) :
    ValidEntryArgs (compactBody spec bSrc) args ↔ ValidEntryArgs bSrc args := by
  unfold ValidEntryArgs compactBody
  dsimp only
  rw [take_drop_paramTys_eq hAbi hTy]

theorem bodyVerified_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    (defId : DefId) (bSrc : Body) (spec : CompactionSpec)
    (hBSrc : Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc)
    (hSpec : Trusted.MirSemantics.getElem? specs defId = some spec)
    (safetyPre : List Val → Prop) :
    BodyVerified pSrc defId bSrc safetyPre ↔
      BodyVerified (compactProgram specs pSrc) defId (compactBody spec bSrc) safetyPre := by
  have hBodyValid := hValid.2 defId bSrc spec hBSrc hSpec
  have hGetTgt := getElem?_compactBodyList_some hBSrc hSpec
  have hAdmitted := bodyStaticAdmitted_compact (specs := specs) (pSrc := pSrc) hBodyValid
  have hValidEntry : ValidProgramCompaction specs (entryProgForBody pSrc defId) := hValid
  have hEntryEq : entryProgForBody (compactProgram specs pSrc) defId =
      compactProgram specs (entryProgForBody pSrc defId) := rfl
  unfold BodyVerified
  constructor
  · intro ⟨_, hAdm, hWf⟩
    refine ⟨hGetTgt, ?_, fun args hArgs hPre => ?_⟩
    · rw [hAdmitted]; exact hAdm
    · have hArgsSrc := (validEntryArgs_compact_iff hBodyValid.1 hBodyValid.2.2.1 args).mp hArgs
      have hWfSrc := hWf args hArgsSrc hPre
      rw [hEntryEq]
      exact (wellFormed_compact_iff hValidEntry { args := args }).mp hWfSrc
  · intro ⟨_, hAdm, hWf⟩
    refine ⟨hBSrc, ?_, fun args hArgs hPre => ?_⟩
    · rw [← hAdmitted]; exact hAdm
    · have hArgsTgt := (validEntryArgs_compact_iff hBodyValid.1 hBodyValid.2.2.1 args).mpr hArgs
      have hWfTgt := hWf args hArgsTgt hPre
      rw [hEntryEq] at hWfTgt
      exact (wellFormed_compact_iff hValidEntry { args := args }).mpr hWfTgt

/-! ### Fuel-Bounded Weakest Precondition (`wpProg`) Transport -/

/-- Structural state-level weakest precondition (`MirWp`-aligned, Pass-1 isolated). -/
noncomputable def wpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
    (∃ c₀ : Choice, ValidChoice p s c₀) ∧
    ∀ c : Choice, ValidChoice p s c →
      match evalStep p c s with
      | .step st' => wpOutcomeState p onDone onFault fuel st'
      | .done out => onDone out
      | .fault k => onFault k

/-- Deterministic `c = 0` evaluation predicate equivalent to `wpOutcomeState`. -/
noncomputable def execOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
    match evalStep p 0 s with
    | .step st' => execOutcomeState p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k

/-- Whole-program fuel-bounded weakest precondition (`initState` + `wpOutcomeState`). -/
noncomputable def wpProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wpOutcomeState p post (fun _ => False) fuel s₀

private theorem wpOutcomeState_iff_execOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {s : State},
      wpOutcomeState p onDone onFault fuel s ↔
      execOutcomeState p onDone onFault fuel s
  | 0, _ => Iff.rfl
  | fuel + 1, s => by
    constructor
    · intro h
      have h0 := h.2 0 rfl
      cases hStep : evalStep p 0 s with
      | step st' =>
        change match evalStep p 0 s with
          | .step st' => wpOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k at h0
        rw [hStep] at h0
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k
        rw [hStep]
        exact wpOutcomeState_iff_execOutcomeState.mp h0
      | done out =>
        change match evalStep p 0 s with
          | .step st' => wpOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k at h0
        rw [hStep] at h0
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k
        rw [hStep]
        exact h0
      | fault k =>
        change match evalStep p 0 s with
          | .step st' => wpOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k at h0
        rw [hStep] at h0
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k
        rw [hStep]
        exact h0
    · intro h
      refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
      change c = 0 at hc
      subst hc
      cases hStep : evalStep p 0 s with
      | step st' =>
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k at h
        rw [hStep] at h
        exact wpOutcomeState_iff_execOutcomeState.mpr h
      | done out =>
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k at h
        rw [hStep] at h
        exact h
      | fault k =>
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p onDone onFault fuel st'
          | .done out => onDone out
          | .fault k => onFault k at h
        rw [hStep] at h
        exact h

private theorem execOutcomeState_fuel_mono {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel₁ fuel₂ : Nat} {s : State},
      fuel₁ ≤ fuel₂ →
      execOutcomeState p onDone onFault fuel₁ s →
      execOutcomeState p onDone onFault fuel₂ s
  | 0, _, _, _, h => False.elim h
  | fuel₁ + 1, 0, _, hLe, _ => False.elim (Nat.not_succ_le_zero fuel₁ hLe)
  | fuel₁ + 1, fuel₂ + 1, s, hLe, h => by
    have hLe' := Nat.le_of_succ_le_succ hLe
    cases hStep : evalStep p 0 s with
    | step st' =>
      change match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel₁ st'
        | .done out => onDone out
        | .fault k => onFault k at h
      rw [hStep] at h
      change match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel₂ st'
        | .done out => onDone out
        | .fault k => onFault k
      rw [hStep]
      exact execOutcomeState_fuel_mono hLe' h
    | done out =>
      change match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel₁ st'
        | .done out => onDone out
        | .fault k => onFault k at h
      rw [hStep] at h
      change match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel₂ st'
        | .done out => onDone out
        | .fault k => onFault k
      rw [hStep]
      exact h
    | fault k =>
      change match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel₁ st'
        | .done out => onDone out
        | .fault k => onFault k at h
      rw [hStep] at h
      change match evalStep p 0 s with
        | .step st' => execOutcomeState p onDone onFault fuel₂ st'
        | .done out => onDone out
        | .fault k => onFault k
      rw [hStep]
      exact h

private theorem execOutcomeState_tgt_of_src {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuel : Nat} {sSrc sTgt : State},
      CompactedStateRel specs pSrc sSrc sTgt →
      execOutcomeState pSrc onDone onFault fuel sSrc →
      execOutcomeState (compactProgram specs pSrc) onDone onFault fuel sTgt
  | 0, _, _, _, h => False.elim h
  | fuel + 1, sSrc, sTgt, hRel, h => by
    cases evalStep_compact_cases hValid hRel with
    | inl hStut =>
      let ⟨sSrc', _, _, hStepSrc, hRel', _⟩ := hStut
      change match evalStep pSrc 0 sSrc with
        | .step st' => execOutcomeState pSrc onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k at h
      rw [hStepSrc] at h
      have hNext := execOutcomeState_tgt_of_src hValid hRel' h
      exact execOutcomeState_fuel_mono (Nat.le_succ fuel) hNext
    | inr hSync =>
      change match evalStep pSrc 0 sSrc with
        | .step st' => execOutcomeState pSrc onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k at h
      change match evalStep (compactProgram specs pSrc) 0 sTgt with
        | .step st' => execOutcomeState (compactProgram specs pSrc) onDone onFault fuel st'
        | .done out => onDone out
        | .fault k => onFault k
      cases hS1 : evalStep pSrc 0 sSrc with
      | step s1 =>
        rw [hS1] at h hSync
        dsimp only at h
        cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
        | step s2 =>
          rw [hS2] at hSync
          dsimp only at hSync
          exact execOutcomeState_tgt_of_src hValid hSync h
        | done _ => rw [hS2] at hSync; exact False.elim hSync
        | fault _ => rw [hS2] at hSync; exact False.elim hSync
      | done o1 =>
        rw [hS1] at h hSync
        dsimp only at h
        cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
        | step _ => rw [hS2] at hSync; exact False.elim hSync
        | done o2 =>
          rw [hS2] at hSync
          dsimp only at hSync
          subst hSync
          exact h
        | fault _ => rw [hS2] at hSync; exact False.elim hSync
      | fault k1 =>
        rw [hS1] at h hSync
        dsimp only at h
        cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
        | step _ => rw [hS2] at hSync; exact False.elim hSync
        | done _ => rw [hS2] at hSync; exact False.elim hSync
        | fault k2 =>
          rw [hS2] at hSync
          dsimp only at hSync
          subst hSync
          exact h

/-- Forward fuel-bounded `wpProg` preservation (`R0 -> R3` never increases step count). -/
theorem wpProg_forward_of_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {fuel : Nat} {q : Query} {post : TerminalOut → Prop}
    (h : wpProg pSrc fuel q post) :
    wpProg (compactProgram specs pSrc) fuel q post := by
  have hInit := initState_compact_equiv hValid q
  unfold wpProg at h; unfold wpProg
  cases hSrc : initState pSrc q with
  | error _ => rw [hSrc] at h; exact False.elim h
  | ok sSrc0 =>
    rw [hSrc] at h hInit
    cases hTgt : initState (compactProgram specs pSrc) q with
    | error _ => rw [hTgt] at hInit; exact False.elim hInit
    | ok sTgt0 =>
      rw [hTgt] at hInit
      exact wpOutcomeState_iff_execOutcomeState.mpr
        (execOutcomeState_tgt_of_src hValid hInit (wpOutcomeState_iff_execOutcomeState.mp h))

/-- Total maximum on `Nat` using `Nat.ble`. -/
noncomputable def natMax (a b : Nat) : Nat :=
  if Nat.ble a b then b else a

private theorem nat_le_natMax_left (a b : Nat) : a ≤ natMax a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | true => exact nat_ble_true_iff.mp h
  | false => exact Nat.le_refl a

private theorem nat_le_natMax_right (a b : Nat) : b ≤ natMax a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl b
  | false => exact Nat.le_of_lt (nat_ble_false_iff.mp h)

/-- Maximum basic-block statement count across a `Body` list. -/
noncomputable def maxBlockStmtsInBlocks : List BasicBlock → Nat
  | [] => 0
  | bb :: bbs => natMax bb.statements.length (maxBlockStmtsInBlocks bbs)

/-- Maximum basic-block statement count across a `Program`. -/
noncomputable def maxBlockStmtsInBodies : List Body → Nat
  | [] => 0
  | b :: bs => natMax (maxBlockStmtsInBlocks b.basicBlocks) (maxBlockStmtsInBodies bs)

private theorem getElem?_le_maxBlockStmtsInBlocks :
    ∀ (bbs : List BasicBlock) (idx : Nat) (bb : BasicBlock),
      Trusted.MirSemantics.getElem? bbs idx = some bb →
      bb.statements.length ≤ maxBlockStmtsInBlocks bbs
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by
    injection h with hEq; subst hEq
    exact nat_le_natMax_left _ _
  | _ :: bbs, idx + 1, bb, h =>
    Nat.le_trans (getElem?_le_maxBlockStmtsInBlocks bbs idx bb h) (nat_le_natMax_right _ _)

private theorem getElem?_le_maxBlockStmtsInBodies :
    ∀ (bs : List Body) (defId : Nat) (b : Body) (bbIdx : Nat) (bb : BasicBlock),
      Trusted.MirSemantics.getElem? bs defId = some b →
      Trusted.MirSemantics.getElem? b.basicBlocks bbIdx = some bb →
      bb.statements.length ≤ maxBlockStmtsInBodies bs
  | [], _, _, _, _, h, _ => by cases h
  | _ :: _, 0, _, bbIdx, bb, hB, hBb => by
    injection hB with hBEq; subst hBEq
    exact Nat.le_trans (getElem?_le_maxBlockStmtsInBlocks _ bbIdx bb hBb) (nat_le_natMax_left _ _)
  | _ :: bs, defId + 1, b, bbIdx, bb, hB, hBb =>
    Nat.le_trans (getElem?_le_maxBlockStmtsInBodies bs defId b bbIdx bb hB hBb) (nat_le_natMax_right _ _)

private theorem sub_le_self (a b : Nat) : a - b ≤ a := by
  induction b generalizing a with
  | zero => exact Nat.le_refl a
  | succ b ih =>
    rw [Nat.sub_succ]
    exact Nat.le_trans (Nat.pred_le _) (ih a)

private theorem flush_execOutcomeState_back {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ (k fuelNext : Nat) {sSrc sTgt : State},
      CompactedStateRel specs pSrc sSrc sTgt →
      (∀ fSrc bSrc bbSrc,
        sSrc.frames = [fSrc] →
        Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
        bbSrc.statements.length - fSrc.stmtIdx ≤ k) →
      (∀ sSrc' sTgt',
        CompactedStateRel specs pSrc sSrc' sTgt' →
        evalStep (compactProgram specs pSrc) 0 sTgt = .step sTgt' →
        execOutcomeState pSrc onDone onFault fuelNext sSrc') →
      (∀ out, evalStep (compactProgram specs pSrc) 0 sTgt = .done out → onDone out) →
      (∀ fk, evalStep (compactProgram specs pSrc) 0 sTgt = .fault fk → onFault fk) →
      execOutcomeState pSrc onDone onFault (fuelNext + (k + 1)) sSrc
  | 0, fuelNext, sSrc, sTgt, hRel, hkBound, hOnStep, hOnDone, hOnFault => by
    cases evalStep_compact_cases hValid hRel with
    | inl hStut =>
      let ⟨_, _, _, _, _, fSrc, _, bSrc, bbSrc, hFS, _, hBS, hBb, hStmt, _, _, _⟩ := hStut
      have hLt := getElem?_eq_some_lt hStmt
      have hGe := Nat.le_of_sub_eq_zero (Nat.le_zero.mp (hkBound fSrc bSrc bbSrc hFS hBS hBb))
      exact False.elim (Nat.not_lt_of_ge hGe hLt)
    | inr hSync =>
      change match evalStep pSrc 0 sSrc with
        | .step st' => execOutcomeState pSrc onDone onFault (fuelNext + 0) st'
        | .done out => onDone out
        | .fault k => onFault k
      cases hS1 : evalStep pSrc 0 sSrc with
      | step s1 =>
        rw [hS1] at hSync
        cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
        | step s2 =>
          rw [hS2] at hSync
          rw [Nat.add_zero]
          exact hOnStep s1 s2 hSync hS2
        | done _ => rw [hS2] at hSync; exact False.elim hSync
        | fault _ => rw [hS2] at hSync; exact False.elim hSync
      | done o1 =>
        rw [hS1] at hSync
        cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
        | step _ => rw [hS2] at hSync; exact False.elim hSync
        | done o2 =>
          rw [hS2] at hSync
          subst hSync
          exact hOnDone o1 hS2
        | fault _ => rw [hS2] at hSync; exact False.elim hSync
      | fault k1 =>
        rw [hS1] at hSync
        cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
        | step _ => rw [hS2] at hSync; exact False.elim hSync
        | done _ => rw [hS2] at hSync; exact False.elim hSync
        | fault k2 =>
          rw [hS2] at hSync
          subst hSync
          exact hOnFault k1 hS2
  | k + 1, fuelNext, sSrc, sTgt, hRel, hkBound, hOnStep, hOnDone, hOnFault => by
    cases evalStep_compact_cases hValid hRel with
    | inr hSync =>
      have hBase : execOutcomeState pSrc onDone onFault (fuelNext + 1) sSrc := by
        change match evalStep pSrc 0 sSrc with
          | .step st' => execOutcomeState pSrc onDone onFault fuelNext st'
          | .done out => onDone out
          | .fault fk => onFault fk
        cases hS1 : evalStep pSrc 0 sSrc with
        | step s1 =>
          rw [hS1] at hSync
          cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
          | step s2 => rw [hS2] at hSync; exact hOnStep s1 s2 hSync hS2
          | done _ => rw [hS2] at hSync; exact False.elim hSync
          | fault _ => rw [hS2] at hSync; exact False.elim hSync
        | done o1 =>
          rw [hS1] at hSync
          cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
          | step _ => rw [hS2] at hSync; exact False.elim hSync
          | done o2 => rw [hS2] at hSync; subst hSync; exact hOnDone o1 hS2
          | fault _ => rw [hS2] at hSync; exact False.elim hSync
        | fault k1 =>
          rw [hS1] at hSync
          cases hS2 : evalStep (compactProgram specs pSrc) 0 sTgt with
          | step _ => rw [hS2] at hSync; exact False.elim hSync
          | done _ => rw [hS2] at hSync; exact False.elim hSync
          | fault k2 => rw [hS2] at hSync; subst hSync; exact hOnFault k1 hS2
      have hLe : fuelNext + 1 ≤ fuelNext + (k + 1 + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.le_add_left 0 (k + 1))) fuelNext
      exact execOutcomeState_fuel_mono hLe hBase
    | inl hStut =>
      let ⟨sSrc', _, _, hStepSrc, hRel', fSrc, fSrc', bSrc, bbSrc, hFS, hFS', hBS, hBb, hStmt, hDef', hBlk', hIdx'⟩ := hStut
      have hBound' : ∀ fS bS bbS,
          sSrc'.frames = [fS] →
          Trusted.MirSemantics.getElem? pSrc.bodies fS.defId = some bS →
          Trusted.MirSemantics.getElem? bS.basicBlocks fS.blockIdx = some bbS →
          bbS.statements.length - fS.stmtIdx ≤ k := by
        intro fS bS bbS hF hB hBlock
        rw [hFS'] at hF; injection hF with hFEq; subst hFEq
        rw [hDef', hBS] at hB; injection hB with hBEq; subst hBEq
        rw [hBlk', hBb] at hBlock; injection hBlock with hBbEq; subst hBbEq
        have hPrev := hkBound fSrc bSrc bbSrc hFS hBS hBb
        have hLt := getElem?_eq_some_lt hStmt
        rw [hIdx']
        cases hRem : bbSrc.statements.length - fSrc.stmtIdx with
        | zero => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero hRem) hLt)
        | succ m =>
          rw [hRem] at hPrev
          rw [Nat.sub_succ, hRem]
          exact Nat.le_of_succ_le_succ hPrev
      have hRec := flush_execOutcomeState_back hValid k fuelNext hRel' hBound' hOnStep hOnDone hOnFault
      change match evalStep pSrc 0 sSrc with
        | .step st' => execOutcomeState pSrc onDone onFault (fuelNext + (k + 1)) st'
        | .done out => onDone out
        | .fault fk => onFault fk
      rw [hStepSrc]
      exact hRec

private theorem execOutcomeState_src_of_tgt {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop} :
    ∀ {fuelTgt : Nat} {sSrc sTgt : State},
      CompactedStateRel specs pSrc sSrc sTgt →
      execOutcomeState (compactProgram specs pSrc) onDone onFault fuelTgt sTgt →
      execOutcomeState pSrc onDone onFault (fuelTgt * (maxBlockStmtsInBodies pSrc.bodies + 1)) sSrc
  | 0, _, _, _, h => False.elim h
  | fuelTgt + 1, sSrc, sTgt, hRel, h => by
    have hBoundM : ∀ fSrc bSrc bbSrc,
        sSrc.frames = [fSrc] →
        Trusted.MirSemantics.getElem? pSrc.bodies fSrc.defId = some bSrc →
        Trusted.MirSemantics.getElem? bSrc.basicBlocks fSrc.blockIdx = some bbSrc →
        bbSrc.statements.length - fSrc.stmtIdx ≤ maxBlockStmtsInBodies pSrc.bodies := by
      intro fSrc bSrc bbSrc _ hBS hBb
      exact Nat.le_trans (sub_le_self _ _) (getElem?_le_maxBlockStmtsInBodies pSrc.bodies fSrc.defId bSrc fSrc.blockIdx bbSrc hBS hBb)
    have hBack := flush_execOutcomeState_back hValid (maxBlockStmtsInBodies pSrc.bodies)
      (fuelTgt * (maxBlockStmtsInBodies pSrc.bodies + 1)) hRel hBoundM
      (fun s1 s2 hRel' hS2 => by
        change match evalStep (compactProgram specs pSrc) 0 sTgt with
          | .step st' => execOutcomeState (compactProgram specs pSrc) onDone onFault fuelTgt st'
          | .done out => onDone out
          | .fault k => onFault k at h
        rw [hS2] at h
        exact execOutcomeState_src_of_tgt hValid hRel' h)
      (fun out hS2 => by
        change match evalStep (compactProgram specs pSrc) 0 sTgt with
          | .step st' => execOutcomeState (compactProgram specs pSrc) onDone onFault fuelTgt st'
          | .done out => onDone out
          | .fault k => onFault k at h
        rw [hS2] at h
        exact h)
      (fun fk hS2 => by
        change match evalStep (compactProgram specs pSrc) 0 sTgt with
          | .step st' => execOutcomeState (compactProgram specs pSrc) onDone onFault fuelTgt st'
          | .done out => onDone out
          | .fault k => onFault k at h
        rw [hS2] at h
        exact h)
    have hMulEq : (fuelTgt + 1) * (maxBlockStmtsInBodies pSrc.bodies + 1) =
        fuelTgt * (maxBlockStmtsInBodies pSrc.bodies + 1) + (maxBlockStmtsInBodies pSrc.bodies + 1) :=
      Nat.succ_mul _ _
    rw [hMulEq]
    exact hBack

/-- Constructive backward fuel-bounded `wpProg` lift from compacted `R3` to `R0`
with explicit bounded multiplier `maxBlockStmtsInBodies pSrc.bodies + 1`. -/
theorem wpProg_backward_of_compact {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    {fuelTgt : Nat} {q : Query} {post : TerminalOut → Prop}
    (h : wpProg (compactProgram specs pSrc) fuelTgt q post) :
    wpProg pSrc (fuelTgt * (maxBlockStmtsInBodies pSrc.bodies + 1)) q post := by
  have hInit := initState_compact_equiv hValid q
  unfold wpProg at h; unfold wpProg
  cases hSrc : initState pSrc q with
  | error _ =>
    rw [hSrc] at hInit
    cases hTgt : initState (compactProgram specs pSrc) q with
    | error _ => rw [hTgt] at h; exact False.elim h
    | ok _ => rw [hTgt] at hInit; exact False.elim hInit
  | ok sSrc0 =>
    rw [hSrc] at hInit
    cases hTgt : initState (compactProgram specs pSrc) q with
    | error _ => rw [hTgt] at hInit; exact False.elim hInit
    | ok sTgt0 =>
      rw [hTgt] at h hInit
      exact wpOutcomeState_iff_execOutcomeState.mpr
        (execOutcomeState_src_of_tgt hValid hInit (wpOutcomeState_iff_execOutcomeState.mp h))

/-- Bidirectional existential `wpProg` transport between `pSrc` (`R0`) and
`compactProgram specs pSrc` (`R3`). -/
theorem wpProg_transport_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    (hValid : ValidProgramCompaction specs pSrc)
    (q : Query) (post : TerminalOut → Prop) :
    (∃ fuelSrc : Nat, wpProg pSrc fuelSrc q post) ↔
      (∃ fuelTgt : Nat, wpProg (compactProgram specs pSrc) fuelTgt q post) := by
  constructor
  · intro ⟨fuelSrc, h⟩
    exact ⟨fuelSrc, wpProg_forward_of_compact hValid h⟩
  · intro ⟨fuelTgt, h⟩
    exact ⟨fuelTgt * (maxBlockStmtsInBodies pSrc.bodies + 1), wpProg_backward_of_compact hValid h⟩

private theorem reaches_execOutcomeState {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s0 s1 : State} (hReach : Reaches p s0 s1) :
    ∀ {fuel : Nat},
      execOutcomeState p onDone onFault fuel s0 →
      ∃ fuel' : Nat, execOutcomeState p onDone onFault fuel' s1 := by
  induction hReach with
  | refl =>
    intro fuel h
    exact ⟨fuel, h⟩
  | tail _ hStep ih =>
    intro fuel h
    let ⟨fuel', h2⟩ := ih h
    cases fuel' with
    | zero => exact False.elim h2
    | succ k =>
      let ⟨c, hc, hEval⟩ := hStep
      change c = 0 at hc; subst hc
      change match evalStep p 0 _ with
        | .step st' => execOutcomeState p onDone onFault k st'
        | .done out => onDone out
        | .fault fk => onFault fk at h2
      rw [hEval] at h2
      exact ⟨k, h2⟩

private theorem execOutcomeState_not_diverges_loop {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {trace : Nat → State}
    (hStep : ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))) :
    ∀ (fuel n : Nat), ¬ execOutcomeState p onDone onFault fuel (trace n)
  | 0, _, h => False.elim h
  | fuel + 1, n, h => by
    let ⟨c, hc, hEval⟩ := hStep n
    change c = 0 at hc; subst hc
    change match evalStep p 0 (trace n) with
      | .step st' => execOutcomeState p onDone onFault fuel st'
      | .done out => onDone out
      | .fault fk => onFault fk at h
    rw [hEval] at h
    exact execOutcomeState_not_diverges_loop hStep fuel (n + 1) h

/-- Soundness connecting local `wpProg` to `Trusted.MirSemantics.SatisfiesPost`
and non-divergence (`¬ Diverges`). -/
theorem satisfiesPost_and_not_diverges_of_wpProg {p : Program} {fuel : Nat}
    {q : Query} {post : TerminalOut → Prop}
    (h : wpProg p fuel q post) :
    SatisfiesPost p q post ∧ ¬ Diverges p q := by
  unfold wpProg at h
  cases hInit : initState p q with
  | error _ => rw [hInit] at h; exact False.elim h
  | ok s0 =>
    rw [hInit] at h
    have hExec0 := wpOutcomeState_iff_execOutcomeState.mp h
    have hNoFault : ∀ k : FaultKind, ¬ ReachesResult p q (.fault k) := by
      intro k hRes
      unfold ReachesResult at hRes
      rw [hInit] at hRes
      let ⟨s, hReach, hFault⟩ := hRes
      let ⟨f', hExecS⟩ := reaches_execOutcomeState hReach hExec0
      cases f' with
      | zero => exact False.elim hExecS
      | succ f'' =>
        let ⟨c, hc, hEval⟩ := hFault
        change c = 0 at hc; subst hc
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p post (fun _ => False) f'' st'
          | .done out => post out
          | .fault fk => False at hExecS
        rw [hEval] at hExecS
        exact False.elim hExecS
    refine ⟨⟨⟨⟨s0, hInit, fun _ _ => ⟨0, rfl⟩⟩, hNoFault⟩, ?_⟩, ?_⟩
    · intro out hBeh
      unfold Behavior ReachesResult at hBeh
      rw [hInit] at hBeh
      let ⟨s, hReach, hDone⟩ := hBeh
      let ⟨f', hExecS⟩ := reaches_execOutcomeState hReach hExec0
      cases f' with
      | zero => exact False.elim hExecS
      | succ f'' =>
        let ⟨c, hc, hEval⟩ := hDone
        change c = 0 at hc; subst hc
        change match evalStep p 0 s with
          | .step st' => execOutcomeState p post (fun _ => False) f'' st'
          | .done out => post out
          | .fault fk => False at hExecS
        rw [hEval] at hExecS
        exact hExecS
    · intro ⟨s0', hInit', trace, h0, hStep⟩
      rw [hInit] at hInit'
      injection hInit' with hEq
      subst hEq
      rw [← h0] at hExec0
      exact execOutcomeState_not_diverges_loop hStep fuel 0 hExec0

private theorem bodies_map_identity_compact :
    ∀ {specs : List CompactionSpec} {bs : List Body},
      specs.length = bs.length →
      (compactBodyList specs bs).map (fun b => b.identity) = bs.map (fun b => b.identity)
  | [], [], _ => rfl
  | _ :: sps, b :: bs, h => by
    change b.identity :: (compactBodyList sps bs).map (fun b => b.identity) =
      b.identity :: bs.map (fun b => b.identity)
    rw [bodies_map_identity_compact (Nat.succ.inj h)]
  | [], _ :: _, h | _ :: _, [], h => by cases h

private theorem compactBodyList_all_nonempty_id :
    ∀ {specs : List CompactionSpec} {bs : List Body},
      specs.length = bs.length →
      (compactBodyList specs bs).all (fun b => !stringBeq b.identity "") =
        bs.all (fun b => !stringBeq b.identity "")
  | [], [], _ => rfl
  | _ :: sps, b :: bs, h => by
    change (!stringBeq b.identity "" && (compactBodyList sps bs).all (fun b => !stringBeq b.identity "")) =
      (!stringBeq b.identity "" && bs.all (fun b => !stringBeq b.identity ""))
    rw [compactBodyList_all_nonempty_id (Nat.succ.inj h)]
  | [], _ :: _, h | _ :: _, [], h => by cases h

private theorem compactBodyList_isEmpty :
    ∀ {specs : List CompactionSpec} {bs : List Body},
      specs.length = bs.length →
      (compactBodyList specs bs).isEmpty = bs.isEmpty
  | [], [], _ => rfl
  | _ :: _, _ :: _, _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by cases h

/-- Bidirectional whole-program `ProgramVerified` transport when `specs.property` is
preserved across compaction (`R0 <-> R3`). -/
theorem programVerified_compact_iff {specs : List CompactionSpec} {pSrc : Program}
    {propSpec : Specs}
    (hValid : ValidProgramCompaction specs pSrc)
    (hProp : propSpec.property pSrc ↔ propSpec.property (compactProgram specs pSrc)) :
    ProgramVerified pSrc propSpec ↔ ProgramVerified (compactProgram specs pSrc) propSpec := by
  unfold ProgramVerified compactProgram
  dsimp only
  have hEmpty : (compactBodyList specs pSrc.bodies).isEmpty = pSrc.bodies.isEmpty :=
    compactBodyList_isEmpty hValid.1
  have hLen : (compactBodyList specs pSrc.bodies).length = pSrc.bodies.length :=
    compactBodyList_length specs pSrc.bodies hValid.1
  have hIds : bodiesHaveUniqueIdentities (compactBodyList specs pSrc.bodies) =
      bodiesHaveUniqueIdentities pSrc.bodies := by
    unfold bodiesHaveUniqueIdentities
    rw [compactBodyList_all_nonempty_id hValid.1, bodies_map_identity_compact hValid.1]
  rw [hEmpty, hLen, hIds]
  constructor
  · intro ⟨hPW, hProf, hNE, hEnt, hUniq, hBodies, hP⟩
    refine ⟨hPW, hProf, hNE, hEnt, hUniq, ?_, hProp.mp hP⟩
    intro defId bTgt hGetTgt
    have hSpec := getElem?_compactBodyList_iff hValid.1 defId
    cases hSrc : Trusted.MirSemantics.getElem? pSrc.bodies defId with
    | none =>
      rw [hSrc] at hSpec
      dsimp only at hSpec
      rw [hSpec.2] at hGetTgt
      cases hGetTgt
    | some bSrc =>
      cases hSp : Trusted.MirSemantics.getElem? specs defId with
      | none =>
        have hGe := getElem?_none_iff.mp hSp
        have hLt := getElem?_eq_some_lt hSrc
        rw [hValid.1] at hGe
        exact False.elim (Nat.not_lt_of_ge hGe hLt)
      | some sp =>
        rw [hSrc, hSp] at hSpec
        dsimp only at hSpec
        rw [hSpec] at hGetTgt
        injection hGetTgt with hEq
        subst hEq
        exact (bodyVerified_compact_iff hValid defId bSrc sp hSrc hSp _).mp (hBodies defId bSrc hSrc)
  · intro ⟨hPW, hProf, hNE, hEnt, hUniq, hBodies, hP⟩
    refine ⟨hPW, hProf, hNE, hEnt, hUniq, ?_, hProp.mpr hP⟩
    intro defId bSrc hSrc
    cases hSp : Trusted.MirSemantics.getElem? specs defId with
    | none =>
      have hGe := getElem?_none_iff.mp hSp
      have hLt := getElem?_eq_some_lt hSrc
      rw [hValid.1] at hGe
      exact False.elim (Nat.not_lt_of_ge hGe hLt)
    | some sp =>
      have hGetTgt := getElem?_compactBodyList_some hSrc hSp
      exact (bodyVerified_compact_iff hValid defId bSrc sp hSrc hSp _).mpr (hBodies defId (compactBody sp bSrc) hGetTgt)

/-!
## Part IV: Fast `O(S)` Positional Stride-8 Certificate Checking vs. `O(S × L)` Linear Association Scanning
-/

/-- Association-list construction pairing local index `base + k` with payload. -/
noncomputable def mkAssocPairs {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | base, x :: xs => (base, x) :: mkAssocPairs (base + 1) xs

/-- Linear `O(L)` association-list lookup (models unindexed linear cert scan). -/
noncomputable def assocLookup {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (k, v) :: rest, i => if Nat.beq k i then some v else assocLookup rest i

/-- Boolean live-mask check via linear `O(L)` association-list scan. -/
noncomputable def assocMaskLookup (pairs : List (Nat × Bool)) (i : Nat) : Bool :=
  match assocLookup pairs i with
  | some b => b
  | none => false

noncomputable def operandLocalsInAssoc (pairs : List (Nat × Bool)) : Operand → Bool
  | .copy p | .move p => assocMaskLookup pairs p.localId
  | .constant _ => true

noncomputable def operandListLocalsInAssoc (pairs : List (Nat × Bool)) : List Operand → Bool
  | [] => true
  | op :: ops => operandLocalsInAssoc pairs op && operandListLocalsInAssoc pairs ops

noncomputable def rvalueLocalsInAssoc (pairs : List (Nat × Bool)) : Rvalue → Bool
  | .use op => operandLocalsInAssoc pairs op
  | .binaryOp _ l r => operandLocalsInAssoc pairs l && operandLocalsInAssoc pairs r
  | .unaryOp _ x => operandLocalsInAssoc pairs x
  | .discriminant p | .ref _ p | .addressOf _ p => assocMaskLookup pairs p.localId
  | .aggregateTuple fs => operandListLocalsInAssoc pairs fs
  | .unsupported => true

noncomputable def stmtLinearAssocCheck (pairs : List (Nat × Bool)) (numLocals : Nat) :
    StatementKind → Bool
  | .assign dst rv => assocMaskLookup pairs dst.localId && rvalueLocalsInAssoc pairs rv
  | .storageLive id => Nat.blt id numLocals && !(assocMaskLookup pairs id)
  | .storageDead id => !Nat.beq id 0 && Nat.blt id numLocals && !(assocMaskLookup pairs id)
  | .nop | .unsupported => true

noncomputable def termLinearAssocCheck (pairs : List (Nat × Bool)) : TerminatorKind → Bool
  | .switchInt discr _ => operandLocalsInAssoc pairs discr
  | .assert cond _ _ _ _ => operandLocalsInAssoc pairs cond
  | .call _ args dst _ _ => operandListLocalsInAssoc pairs args && assocMaskLookup pairs dst.localId
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true

noncomputable def linearAssocAllStmts (pairs : List (Nat × Bool)) (numLocals : Nat) :
    List StatementKind → Bool
  | [] => true
  | s :: ss => stmtLinearAssocCheck pairs numLocals s && linearAssocAllStmts pairs numLocals ss

noncomputable def linearAssocAllBlocks (pairs : List (Nat × Bool)) (numLocals : Nat) :
    List BasicBlock → Bool
  | [] => true
  | bb :: bbs =>
    linearAssocAllStmts pairs numLocals bb.statements &&
    termLinearAssocCheck pairs bb.terminator &&
    linearAssocAllBlocks pairs numLocals bbs

/-- `O(S × L)` linear association-list compaction checker (models unindexed cert checking). -/
noncomputable def checkR3LinearAssoc (bSrc : Body) (spec : CompactionSpec) : Bool :=
  Nat.beq spec.liveMask.length bSrc.locals.length &&
  Nat.blt bSrc.argumentCount spec.liveMask.length &&
  Nat.blt bSrc.argumentCount spec.targetLocals.length &&
  spec.targetLocals.all isSupportedScalarOrUnitTy &&
  bSrc.locals.all isSupportedScalarOrUnitTy &&
  checkAbiLoop bSrc.argumentCount spec bSrc.argumentCount &&
  checkInjectiveLoop spec bSrc.locals.length bSrc.locals.length &&
  checkTargetTypesLoop bSrc spec bSrc.locals.length &&
  linearAssocAllBlocks (mkAssocPairs 0 spec.liveMask) bSrc.locals.length bSrc.basicBlocks

private theorem nat_beq_base_lt_false :
    ∀ {a b : Nat}, a < b → Nat.beq a b = false
  | _, 0, h => False.elim (Nat.not_lt_zero _ h)
  | 0, .succ _, _ => rfl
  | .succ a, .succ b, h => by
    change Nat.beq a b = false
    exact nat_beq_base_lt_false (Nat.lt_of_succ_lt_succ h)

private theorem assocLookup_mkAssocPairs_ge {α : Type} :
    ∀ (xs : List α) (base i : Nat),
      base ≤ i →
      assocLookup (mkAssocPairs base xs) i = Trusted.MirSemantics.getElem? xs (i - base)
  | [], _, _, _ => rfl
  | x :: xs, base, i, hLe => by
    cases Nat.eq_or_lt_of_le hLe with
    | inl hEq =>
      subst hEq
      have hSub : base - base = 0 := Nat.sub_self base
      unfold mkAssocPairs assocLookup
      rw [bool_ite_pos (nat_beq_refl base), hSub]
      rfl
    | inr hLt =>
      have hNe : Nat.beq base i = false := nat_beq_base_lt_false hLt
      have hSuccLe : base + 1 ≤ i := hLt
      unfold mkAssocPairs assocLookup
      rw [bool_ite_neg hNe, assocLookup_mkAssocPairs_ge xs (base + 1) i hSuccLe]
      cases hRem : i - base with
      | zero => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero hRem) hLt)
      | succ d =>
        have hSubSucc : i - (base + 1) = d := by
          rw [Nat.sub_succ, hRem]
          rfl
        rw [hSubSucc]
        rfl

private theorem assocMaskLookup_eq_isLiveLocal (mask : List Bool) (i : Nat) :
    assocMaskLookup (mkAssocPairs 0 mask) i = isLiveLocal mask i := by
  unfold assocMaskLookup isLiveLocal
  rw [assocLookup_mkAssocPairs_ge mask 0 i (Nat.zero_le i), Nat.sub_zero]

private theorem operandListLocalsInAssoc_eq (mask : List Bool) :
    ∀ ops : List Operand, operandListLocalsInAssoc (mkAssocPairs 0 mask) ops = operandListLocalsInMask mask ops
  | [] => rfl
  | op :: ops => by
    change (operandLocalsInAssoc (mkAssocPairs 0 mask) op && operandListLocalsInAssoc (mkAssocPairs 0 mask) ops) =
      (operandLocalsInMask mask op && operandListLocalsInMask mask ops)
    have hop : operandLocalsInAssoc (mkAssocPairs 0 mask) op = operandLocalsInMask mask op := by
      cases op with | constant _ => rfl | copy p | move p => unfold operandLocalsInAssoc operandLocalsInMask; dsimp only; rw [assocMaskLookup_eq_isLiveLocal]
    rw [hop, operandListLocalsInAssoc_eq mask ops]

private theorem linearAssocStmts_sound (mask : List Bool) (numLocals : Nat) :
    ∀ stms : List StatementKind,
      linearAssocAllStmts (mkAssocPairs 0 mask) numLocals stms = true →
      stms.all (stmtRefLocalsInMask mask) = true ∧ stms.all (stmtStorageOnlyOnDead mask numLocals) = true
  | [] => fun _ => ⟨rfl, rfl⟩
  | s :: ss => fun hSt => by
    change (stmtLinearAssocCheck (mkAssocPairs 0 mask) numLocals s &&
      linearAssocAllStmts (mkAssocPairs 0 mask) numLocals ss) = true at hSt
    cases hs1 : stmtLinearAssocCheck (mkAssocPairs 0 mask) numLocals s with
    | false => rw [hs1] at hSt; cases hSt
    | true =>
      rw [hs1] at hSt
      let ⟨ihs1, ihs2⟩ := linearAssocStmts_sound mask numLocals ss hSt
      have hRefS : stmtRefLocalsInMask mask s = true := by
        cases s with
        | nop | storageLive _ | storageDead _ | unsupported => rfl
        | assign dst rv =>
          unfold stmtLinearAssocCheck at hs1; dsimp only at hs1
          unfold stmtRefLocalsInMask; dsimp only
          have hRvEq : rvalueLocalsInAssoc (mkAssocPairs 0 mask) rv = rvalueLocalsInMask mask rv := by
            cases rv with
            | use op =>
              unfold rvalueLocalsInAssoc rvalueLocalsInMask; dsimp only
              cases op with
              | constant _ => rfl
              | copy p | move p => unfold operandLocalsInAssoc operandLocalsInMask; dsimp only; rw [assocMaskLookup_eq_isLiveLocal]
            | binaryOp _ l r =>
              unfold rvalueLocalsInAssoc rvalueLocalsInMask; dsimp only
              have hl : operandLocalsInAssoc (mkAssocPairs 0 mask) l = operandLocalsInMask mask l := by
                cases l with | constant _ => rfl | copy p | move p => unfold operandLocalsInAssoc operandLocalsInMask; dsimp only; rw [assocMaskLookup_eq_isLiveLocal]
              have hr : operandLocalsInAssoc (mkAssocPairs 0 mask) r = operandLocalsInMask mask r := by
                cases r with | constant _ => rfl | copy p | move p => unfold operandLocalsInAssoc operandLocalsInMask; dsimp only; rw [assocMaskLookup_eq_isLiveLocal]
              rw [hl, hr]
            | unaryOp _ x =>
              unfold rvalueLocalsInAssoc rvalueLocalsInMask; dsimp only
              cases x with | constant _ => rfl | copy p | move p => unfold operandLocalsInAssoc operandLocalsInMask; dsimp only; rw [assocMaskLookup_eq_isLiveLocal]
            | discriminant p | ref _ p | addressOf _ p =>
              unfold rvalueLocalsInAssoc rvalueLocalsInMask; dsimp only
              rw [assocMaskLookup_eq_isLiveLocal]
            | aggregateTuple fs =>
              unfold rvalueLocalsInAssoc rvalueLocalsInMask; dsimp only
              exact operandListLocalsInAssoc_eq mask fs
            | unsupported => rfl
          rw [assocMaskLookup_eq_isLiveLocal, hRvEq] at hs1
          exact hs1
      have hDeadS : stmtStorageOnlyOnDead mask numLocals s = true := by
        cases s with
        | nop | assign _ _ | unsupported => rfl
        | storageLive id =>
          unfold stmtLinearAssocCheck at hs1; dsimp only at hs1
          unfold stmtStorageOnlyOnDead; dsimp only
          rw [assocMaskLookup_eq_isLiveLocal] at hs1
          exact hs1
        | storageDead id =>
          unfold stmtLinearAssocCheck at hs1; dsimp only at hs1
          unfold stmtStorageOnlyOnDead; dsimp only
          rw [assocMaskLookup_eq_isLiveLocal] at hs1
          exact hs1
      refine ⟨?_, ?_⟩
      · change (stmtRefLocalsInMask mask s && ss.all (stmtRefLocalsInMask mask)) = true
        rw [hRefS, ihs1]; rfl
      · change (stmtStorageOnlyOnDead mask numLocals s && ss.all (stmtStorageOnlyOnDead mask numLocals)) = true
        rw [hDeadS, ihs2]; rfl

private theorem linearAssocBlocks_sound {mask : List Bool} {numLocals : Nat} {bbs : List BasicBlock}
    (h : linearAssocAllBlocks (mkAssocPairs 0 mask) numLocals bbs = true) :
    bbs.all (fun bb =>
      bb.statements.all (stmtRefLocalsInMask mask) &&
      termLocalsInMask mask bb.terminator) = true ∧
    bbs.all (fun bb => bb.statements.all (stmtStorageOnlyOnDead mask numLocals)) = true := by
  induction bbs with
  | nil => exact ⟨rfl, rfl⟩
  | cons bb bbs ih =>
    change ((linearAssocAllStmts (mkAssocPairs 0 mask) numLocals bb.statements &&
      termLinearAssocCheck (mkAssocPairs 0 mask) bb.terminator) &&
      linearAssocAllBlocks (mkAssocPairs 0 mask) numLocals bbs) = true at h
    cases hSt : linearAssocAllStmts (mkAssocPairs 0 mask) numLocals bb.statements with
    | false => rw [hSt] at h; cases h
    | true =>
      rw [hSt] at h
      cases hTm : termLinearAssocCheck (mkAssocPairs 0 mask) bb.terminator with
      | false => rw [hTm] at h; cases h
      | true =>
        rw [hTm] at h
        let ⟨ihRef, ihDead⟩ := ih h
        have hStPair := linearAssocStmts_sound mask numLocals bb.statements hSt
        have hTmEq : termLocalsInMask mask bb.terminator = true := by
          cases hTerm : bb.terminator with
          | goto _ | return_ | unreachable | unwindResume | unsupported => rfl
          | switchInt d _ =>
            rw [hTerm] at hTm
            unfold termLinearAssocCheck at hTm; dsimp only at hTm
            unfold termLocalsInMask
            cases d with
            | constant _ => rfl
            | copy p | move p => unfold operandLocalsInAssoc at hTm; unfold operandLocalsInMask; dsimp only at hTm; dsimp only; rw [assocMaskLookup_eq_isLiveLocal] at hTm; exact hTm
          | assert c _ _ _ _ =>
            rw [hTerm] at hTm
            unfold termLinearAssocCheck at hTm; dsimp only at hTm
            unfold termLocalsInMask
            cases c with
            | constant _ => rfl
            | copy p | move p => unfold operandLocalsInAssoc at hTm; unfold operandLocalsInMask; dsimp only at hTm; dsimp only; rw [assocMaskLookup_eq_isLiveLocal] at hTm; exact hTm
          | call _ args dst _ _ =>
            rw [hTerm] at hTm
            unfold termLinearAssocCheck at hTm; dsimp only at hTm
            unfold termLocalsInMask
            have hListEq := operandListLocalsInAssoc_eq mask args
            rw [hListEq, assocMaskLookup_eq_isLiveLocal] at hTm
            exact hTm
        refine ⟨?_, ?_⟩
        · change ((bb.statements.all (stmtRefLocalsInMask mask) && termLocalsInMask mask bb.terminator) &&
            bbs.all (fun bb => bb.statements.all (stmtRefLocalsInMask mask) && termLocalsInMask mask bb.terminator)) = true
          rw [hStPair.1, hTmEq, ihRef]; rfl
        · change (bb.statements.all (stmtStorageOnlyOnDead mask numLocals) &&
            bbs.all (fun bb => bb.statements.all (stmtStorageOnlyOnDead mask numLocals))) = true
          rw [hStPair.2, ihDead]; rfl

theorem validBodyCompaction_of_checkR3LinearAssoc {bSrc : Body} {spec : CompactionSpec}
    (h : checkR3LinearAssoc bSrc spec = true) : ValidBodyCompaction bSrc spec := by
  unfold checkR3LinearAssoc at h
  cases h1 : Nat.beq spec.liveMask.length bSrc.locals.length with
  | false => rw [h1] at h; cases h
  | true =>
    rw [h1] at h
    cases h2 : Nat.blt bSrc.argumentCount spec.liveMask.length with
    | false => rw [h2] at h; cases h
    | true =>
      rw [h2] at h
      cases h3 : Nat.blt bSrc.argumentCount spec.targetLocals.length with
      | false => rw [h3] at h; cases h
      | true =>
        rw [h3] at h
        cases h4 : spec.targetLocals.all isSupportedScalarOrUnitTy with
        | false => rw [h4] at h; cases h
        | true =>
          rw [h4] at h
          cases h5 : bSrc.locals.all isSupportedScalarOrUnitTy with
          | false => rw [h5] at h; cases h
          | true =>
            rw [h5] at h
            cases h6 : checkAbiLoop bSrc.argumentCount spec bSrc.argumentCount with
            | false => rw [h6] at h; cases h
            | true =>
              rw [h6] at h
              cases h7 : checkInjectiveLoop spec bSrc.locals.length bSrc.locals.length with
              | false => rw [h7] at h; cases h
              | true =>
                rw [h7] at h
                cases h8 : checkTargetTypesLoop bSrc spec bSrc.locals.length with
                | false => rw [h8] at h; cases h
                | true =>
                  rw [h8] at h
                  have hLenEq : spec.liveMask.length = bSrc.locals.length := nat_beq_eq h1
                  have hAbi : PreservesAbiSlots bSrc.argumentCount spec :=
                    ⟨nat_blt_true_iff.mp h2, checkAbiLoop_sound bSrc.argumentCount h6⟩
                  have hInj : InjectiveOnLive spec := by
                    intro i j hi hj hMap
                    have hiLt : i < bSrc.locals.length := by
                      rw [← hLenEq]
                      exact isLiveLocal_eq_true_lt hi
                    have hjLt : j < bSrc.locals.length := by
                      rw [← hLenEq]
                      exact isLiveLocal_eq_true_lt hj
                    exact checkInjectiveLoop_sound bSrc.locals.length bSrc.locals.length h7 i j hiLt hjLt hi hj hMap
                  have hTy : ValidTargetTypes bSrc spec := by
                    refine ⟨hLenEq, nat_blt_true_iff.mp h3, h4, h5, ?_⟩
                    intro i hi
                    have hiLt : i < bSrc.locals.length := by
                      rw [← hLenEq]
                      exact isLiveLocal_eq_true_lt hi
                    exact checkTargetTypesLoop_sound bSrc.locals.length h8 i hiLt hi
                  let ⟨hRef, hDead⟩ := linearAssocBlocks_sound h
                  exact ⟨hAbi, hInj, hTy, hRef, hDead⟩

/-! ### Balanced Radix-8 `MaskTree` (`O(log L)` lookup) and Stride-8 Positional Checker (`O(S)`) -/

inductive MaskTree where
  | leaf8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool)
  | leafList (xs : List Bool)
  | node (szL : Nat) (l r : MaskTree)

noncomputable def maskTreeFlatten : MaskTree → List Bool
  | .leaf8 b0 b1 b2 b3 b4 b5 b6 b7 => [b0, b1, b2, b3, b4, b5, b6, b7]
  | .leafList xs => xs
  | .node _ l r => maskTreeFlatten l ++ maskTreeFlatten r

noncomputable def maskTreeGet : MaskTree → Nat → Bool
  | .leaf8 b0 b1 b2 b3 b4 b5 b6 b7, i =>
    match i with
    | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    | 4 => b4 | 5 => b5 | 6 => b6 | 7 => b7
    | _ => false
  | .leafList xs, i => isLiveLocal xs i
  | .node szL l r, i =>
    if Nat.blt i szL then maskTreeGet l i else maskTreeGet r (i - szL)

noncomputable def mkMaskLeaves8 : List Bool → List (Nat × MaskTree)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    (8, .leaf8 b0 b1 b2 b3 b4 b5 b6 b7) :: mkMaskLeaves8 rest
  | xs => [(xs.length, .leafList xs)]

noncomputable def mergePairRound : List (Nat × MaskTree) → List (Nat × MaskTree)
  | (s1, t1) :: (s2, t2) :: rest => (s1 + s2, .node s1 t1 t2) :: mergePairRound rest
  | rest => rest

noncomputable def foldMaskTrees : Nat → List (Nat × MaskTree) → MaskTree
  | _, [] => .leafList []
  | _, [(_, t)] => t
  | 0, (_, t) :: _ => t
  | fuel + 1, ts => foldMaskTrees fuel (mergePairRound ts)

/-- Build a balanced radix-8 binary `MaskTree` in `O(L)` total work (depth ≤ `⌈log₂(L/8)⌉`). -/
noncomputable def buildMaskTree (xs : List Bool) : MaskTree :=
  let leaves := mkMaskLeaves8 xs
  foldMaskTrees leaves.length leaves

private theorem list_append_nil {α : Type} : ∀ (xs : List α), xs ++ [] = xs
  | [] => rfl
  | x :: xs => congrArg (List.cons x) (list_append_nil xs)

private theorem list_append_assoc {α : Type} :
    ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | x :: xs, ys, zs => congrArg (List.cons x) (list_append_assoc xs ys zs)

private theorem list_append_length {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [], ys => by change ys.length = 0 + ys.length; rw [Nat.zero_add]
  | _ :: xs, ys => by
    change ((xs ++ ys).length + 1) = (xs.length + 1) + ys.length
    rw [list_append_length xs ys, Nat.add_right_comm]

private theorem getElem?_append {α : Type} :
    ∀ (xs ys : List α) (i : Nat),
      Trusted.MirSemantics.getElem? (xs ++ ys) i =
        if Nat.blt i xs.length then Trusted.MirSemantics.getElem? xs i
        else Trusted.MirSemantics.getElem? ys (i - xs.length)
  | [], ys, i => by
    change Trusted.MirSemantics.getElem? ys i =
      if Nat.blt i 0 then none else Trusted.MirSemantics.getElem? ys (i - 0)
    have hF : Nat.blt i 0 = false := rfl
    rw [bool_ite_neg hF, Nat.sub_zero]
  | _ :: _, _, 0 => rfl
  | _ :: xs, ys, n + 1 => by
    change Trusted.MirSemantics.getElem? (xs ++ ys) n =
      if Nat.blt (n + 1) (xs.length + 1) then Trusted.MirSemantics.getElem? xs n
      else Trusted.MirSemantics.getElem? ys ((n + 1) - (xs.length + 1))
    rw [getElem?_append xs ys n]
    have hEqBlt : Nat.blt (n + 1) (xs.length + 1) = Nat.blt n xs.length := rfl
    have hEqSub : (n + 1) - (xs.length + 1) = n - xs.length := Nat.succ_sub_succ n xs.length
    cases hB : Nat.blt n xs.length with
    | true =>
      have hB' : Nat.blt (n + 1) (xs.length + 1) = true := by rw [hEqBlt, hB]
      rw [bool_ite_pos (rfl : true = true), bool_ite_pos hB']
    | false =>
      have hB' : Nat.blt (n + 1) (xs.length + 1) = false := by rw [hEqBlt, hB]
      rw [bool_ite_neg (rfl : false = false), bool_ite_neg hB', hEqSub]

noncomputable def MaskTreeValid : MaskTree → Prop
  | .leaf8 _ _ _ _ _ _ _ _ => True
  | .leafList _ => True
  | .node szL l r => szL = (maskTreeFlatten l).length ∧ MaskTreeValid l ∧ MaskTreeValid r

private theorem maskTreeGet_eq_isLiveLocal :
    ∀ {t : MaskTree}, MaskTreeValid t → ∀ i : Nat,
      maskTreeGet t i = isLiveLocal (maskTreeFlatten t) i
  | .leaf8 b0 b1 b2 b3 b4 b5 b6 b7, _, i => by
    cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => cases i with
        | zero => rfl
        | succ i => cases i with
          | zero => rfl
          | succ i => cases i with
            | zero => rfl
            | succ i => cases i with
              | zero => rfl
              | succ i => cases i with
                | zero => rfl
                | succ i => cases i with
                  | zero => rfl
                  | succ _ => rfl
  | .leafList xs, _, _ => rfl
  | .node szL l r, ⟨hSz, hL, hR⟩, i => by
    unfold maskTreeGet maskTreeFlatten isLiveLocal
    rw [getElem?_append, ← hSz]
    cases hBlt : Nat.blt i szL with
    | true =>
      rw [bool_ite_pos (rfl : true = true), bool_ite_pos (rfl : true = true)]
      exact maskTreeGet_eq_isLiveLocal hL i
    | false =>
      rw [bool_ite_neg (rfl : false = false), bool_ite_neg (rfl : false = false)]
      exact maskTreeGet_eq_isLiveLocal hR (i - szL)

noncomputable def flattenPairs : List (Nat × MaskTree) → List Bool
  | [] => []
  | (_, t) :: ts => maskTreeFlatten t ++ flattenPairs ts

noncomputable def PairsValid : List (Nat × MaskTree) → Prop
  | [] => True
  | p :: ts => p.1 = (maskTreeFlatten p.2).length ∧ MaskTreeValid p.2 ∧ PairsValid ts

private theorem mkMaskLeaves8_spec :
    ∀ xs : List Bool,
      flattenPairs (mkMaskLeaves8 xs) = xs ∧ PairsValid (mkMaskLeaves8 xs)
  | [] => ⟨rfl, ⟨rfl, True.intro, True.intro⟩⟩
  | [_] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | [_, _] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | [_, _, _] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | [_, _, _, _] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | [_, _, _, _, _] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | [_, _, _, _, _, _] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | [_, _, _, _, _, _, _] => ⟨list_append_nil _, ⟨rfl, True.intro, True.intro⟩⟩
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => by
    let ⟨hFl, hVal⟩ := mkMaskLeaves8_spec rest
    unfold mkMaskLeaves8 flattenPairs
    dsimp only [maskTreeFlatten]
    refine ⟨?_, rfl, True.intro, hVal⟩
    change b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: flattenPairs (mkMaskLeaves8 rest) = _
    rw [hFl]

private theorem mergePairRound_spec :
    ∀ ts : List (Nat × MaskTree),
      flattenPairs (mergePairRound ts) = flattenPairs ts ∧
      (PairsValid ts → PairsValid (mergePairRound ts)) ∧
      (mergePairRound ts).length ≤ ts.length
  | [] => ⟨rfl, fun h => h, Nat.le_refl 0⟩
  | [(s, t)] => ⟨rfl, fun h => h, Nat.le_refl 1⟩
  | (s1, t1) :: (s2, t2) :: rest => by
    let ⟨hFl, hVal, hLen⟩ := mergePairRound_spec rest
    refine ⟨?_, ?_, ?_⟩
    · unfold mergePairRound flattenPairs
      dsimp only [maskTreeFlatten]
      rw [list_append_assoc, hFl]
      rfl
    · intro ⟨hs1, ht1, hs2, ht2, hRest⟩
      dsimp only at hs1 ht1 hs2 ht2
      refine ⟨?_, ⟨hs1, ht1, ht2⟩, hVal hRest⟩
      dsimp only [maskTreeFlatten]
      rw [list_append_length, hs1, hs2]
    · change (mergePairRound rest).length + 1 ≤ rest.length + 2
      exact Nat.le_trans (Nat.succ_le_succ hLen) (Nat.le_succ _)

private theorem foldMaskTrees_spec :
    ∀ (fuel : Nat) (ts : List (Nat × MaskTree)),
      ts.length ≤ fuel + 1 →
      PairsValid ts →
      maskTreeFlatten (foldMaskTrees fuel ts) = flattenPairs ts ∧
      MaskTreeValid (foldMaskTrees fuel ts)
  | 0, [], _, _ => ⟨rfl, True.intro⟩
  | _ + 1, [], _, _ => ⟨rfl, True.intro⟩
  | 0, [(_, t)], _, ⟨_, ht, _⟩ => ⟨(list_append_nil _).symm, ht⟩
  | _ + 1, [(_, t)], _, ⟨_, ht, _⟩ => ⟨(list_append_nil _).symm, ht⟩
  | 0, _ :: _ :: rest, hLe, _ =>
    False.elim (Nat.not_succ_le_zero rest.length (Nat.le_of_succ_le_succ hLe))
  | fuel + 1, a :: b :: rest, hLe, hVal => by
    let ⟨_, _, hLenRest⟩ := mergePairRound_spec rest
    let ⟨hFullFl, hFullValFn, _⟩ := mergePairRound_spec (a :: b :: rest)
    have hFullVal : PairsValid (mergePairRound (a :: b :: rest)) := hFullValFn hVal
    have hLenBound : (mergePairRound (a :: b :: rest)).length ≤ fuel + 1 := by
      change (mergePairRound rest).length + 1 ≤ fuel + 1
      have hRestLe : rest.length + 1 ≤ fuel + 1 :=
        Nat.le_of_succ_le_succ hLe
      exact Nat.le_trans (Nat.succ_le_succ hLenRest) hRestLe
    let ⟨hRecFl, hRecVal⟩ := foldMaskTrees_spec fuel (mergePairRound (a :: b :: rest)) hLenBound hFullVal
    unfold foldMaskTrees
    rw [hRecFl, hFullFl]
    exact ⟨rfl, hRecVal⟩

private theorem maskTreeGet_buildMaskTree (mask : List Bool) (i : Nat) :
    maskTreeGet (buildMaskTree mask) i = isLiveLocal mask i := by
  let leaves := mkMaskLeaves8 mask
  let ⟨hFl, hVal⟩ := mkMaskLeaves8_spec mask
  have hLe : leaves.length ≤ leaves.length + 1 := Nat.le_succ _
  let ⟨hFoldFl, hFoldVal⟩ := foldMaskTrees_spec leaves.length leaves hLe hVal
  change maskTreeGet (foldMaskTrees leaves.length leaves) i = isLiveLocal mask i
  rw [maskTreeGet_eq_isLiveLocal hFoldVal i, hFoldFl, hFl]

/-- One lockstep validation step across `(bSrc.locals, spec.liveMask, spec.slotMap, spec.targetLocals)`. -/
noncomputable def checkZipStep (argc srcIdx expTgtIdx : Nat)
    (srcTy : MirTy) (b : Bool) (tgtIdx : Nat) (tgts : List MirTy) :
    Option (Nat × List MirTy) :=
  match isSupportedScalarOrUnitTy srcTy with
  | false => none
  | true =>
    match Nat.ble srcIdx argc && !b with
    | true => none
    | false =>
      match b with
      | false => some (expTgtIdx, tgts)
      | true =>
        match Nat.beq tgtIdx expTgtIdx with
        | false => none
        | true =>
          match tgts with
          | [] => none
          | tgtTy :: tgtsRest =>
            match MirTy.beq srcTy tgtTy with
            | true => some (expTgtIdx + 1, tgtsRest)
            | false => none

/-- Sequential `O(L)` lockstep validator proving `PreservesAbiSlots`, strict-monotone
`InjectiveOnLive`, and `ValidTargetTypes` simultaneously. -/
noncomputable def checkZipLocals (argc srcIdx expTgtIdx : Nat) :
    List MirTy → List Bool → List Nat → List MirTy → Bool
  | [], [], [], [] => Nat.blt argc expTgtIdx && Nat.blt argc srcIdx
  | ty :: tys, b :: bs, m :: ms, tgts =>
    match checkZipStep argc srcIdx expTgtIdx ty b m tgts with
    | none => false
    | some (nextTgt, tgtsRest) =>
      checkZipLocals argc (srcIdx + 1) nextTgt tys bs ms tgtsRest
  | _, _, _, _ => false

/-- Stride-8 batched `O(L)` lockstep validator avoiding `maxRecDepth` stacks on large frames. -/
noncomputable def checkZipLocals8 (argc srcIdx expTgtIdx : Nat) :
    List MirTy → List Bool → List Nat → List MirTy → Bool
  | s0::s1::s2::s3::s4::s5::s6::s7::tys,
    b0::b1::b2::b3::b4::b5::b6::b7::bs,
    m0::m1::m2::m3::m4::m5::m6::m7::ms, tgts =>
    match checkZipStep argc srcIdx expTgtIdx s0 b0 m0 tgts with
    | none => false
    | some (e1, t1) =>
      match checkZipStep argc (srcIdx + 1) e1 s1 b1 m1 t1 with
      | none => false
      | some (e2, t2) =>
        match checkZipStep argc (srcIdx + 2) e2 s2 b2 m2 t2 with
        | none => false
        | some (e3, t3) =>
          match checkZipStep argc (srcIdx + 3) e3 s3 b3 m3 t3 with
          | none => false
          | some (e4, t4) =>
            match checkZipStep argc (srcIdx + 4) e4 s4 b4 m4 t4 with
            | none => false
            | some (e5, t5) =>
              match checkZipStep argc (srcIdx + 5) e5 s5 b5 m5 t5 with
              | none => false
              | some (e6, t6) =>
                match checkZipStep argc (srcIdx + 6) e6 s6 b6 m6 t6 with
                | none => false
                | some (e7, t7) =>
                  match checkZipStep argc (srcIdx + 7) e7 s7 b7 m7 t7 with
                  | none => false
                  | some (e8, t8) =>
                    checkZipLocals8 argc (srcIdx + 8) e8 tys bs ms t8
  | tys, bs, ms, tgts => checkZipLocals argc srcIdx expTgtIdx tys bs ms tgts

private theorem checkZipLocals8_eq :
    ∀ (argc srcIdx expTgtIdx : Nat) (tys : List MirTy) (bs : List Bool) (ms : List Nat) (tgts : List MirTy),
      checkZipLocals8 argc srcIdx expTgtIdx tys bs ms tgts =
      checkZipLocals argc srcIdx expTgtIdx tys bs ms tgts
  | _, _, _, [], _, _, _ | _, _, _, [_], _, _, _ | _, _, _, [_, _], _, _, _
  | _, _, _, [_, _, _], _, _, _ | _, _, _, [_, _, _, _], _, _, _
  | _, _, _, [_, _, _, _, _], _, _, _ | _, _, _, [_, _, _, _, _, _], _, _, _
  | _, _, _, [_, _, _, _, _, _, _], _, _, _ => rfl
  | _, _, _, _::_::_::_::_::_::_::_::_, [], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _, _], _, _ => rfl
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _, _], _ => rfl
  | argc, srcIdx, expTgtIdx,
    s0::s1::s2::s3::s4::s5::s6::s7::tys,
    b0::b1::b2::b3::b4::b5::b6::b7::bs,
    m0::m1::m2::m3::m4::m5::m6::m7::ms, tgts => by
    unfold checkZipLocals8
    cases h0 : checkZipStep argc srcIdx expTgtIdx s0 b0 m0 tgts with
    | none => unfold checkZipLocals; rw [h0]
    | some p1 =>
      rw [checkZipLocals.eq_2, h0]; dsimp only
      cases h1 : checkZipStep argc (srcIdx + 1) p1.1 s1 b1 m1 p1.2 with
      | none => unfold checkZipLocals; rw [h1]
      | some p2 =>
        rw [checkZipLocals.eq_2, h1]; dsimp only
        cases h2 : checkZipStep argc (srcIdx + 2) p2.1 s2 b2 m2 p2.2 with
        | none => unfold checkZipLocals; rw [h2]
        | some p3 =>
          rw [checkZipLocals.eq_2, h2]; dsimp only
          cases h3 : checkZipStep argc (srcIdx + 3) p3.1 s3 b3 m3 p3.2 with
          | none => unfold checkZipLocals; rw [h3]
          | some p4 =>
            rw [checkZipLocals.eq_2, h3]; dsimp only
            cases h4 : checkZipStep argc (srcIdx + 4) p4.1 s4 b4 m4 p4.2 with
            | none => unfold checkZipLocals; rw [h4]
            | some p5 =>
              rw [checkZipLocals.eq_2, h4]; dsimp only
              cases h5 : checkZipStep argc (srcIdx + 5) p5.1 s5 b5 m5 p5.2 with
              | none => unfold checkZipLocals; rw [h5]
              | some p6 =>
                rw [checkZipLocals.eq_2, h5]; dsimp only
                cases h6 : checkZipStep argc (srcIdx + 6) p6.1 s6 b6 m6 p6.2 with
                | none => unfold checkZipLocals; rw [h6]
                | some p7 =>
                  rw [checkZipLocals.eq_2, h6]; dsimp only
                  cases h7 : checkZipStep argc (srcIdx + 7) p7.1 s7 b7 m7 p7.2 with
                  | none => unfold checkZipLocals; rw [h7]
                  | some p8 =>
                    rw [checkZipLocals.eq_2, h7]; dsimp only
                    exact checkZipLocals8_eq argc (srcIdx + 8) p8.1 tys bs ms p8.2

private theorem sub_succ_eq_sub_add_one :
    ∀ {b a : Nat}, b + 1 ≤ a → a - b = (a - (b + 1)) + 1
  | 0, 0, h => False.elim (Nat.not_succ_le_zero 0 h)
  | 0, a + 1, _ => rfl
  | b + 1, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | b + 1, a + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    exact sub_succ_eq_sub_add_one (Nat.le_of_succ_le_succ h)

private theorem add_succ_right_comm (a k : Nat) :
    a + (k + 1) = (a + 1) + k := by
  rw [Nat.add_assoc a 1 k, Nat.add_comm 1 k]

private theorem checkZipLocals_sound :
    ∀ (argc srcIdx expTgtIdx : Nat) (srcs : List MirTy) (bs : List Bool) (ms : List Nat) (tgts : List MirTy),
      checkZipLocals argc srcIdx expTgtIdx srcs bs ms tgts = true →
      (srcIdx ≤ argc → expTgtIdx = srcIdx) →
      bs.length = srcs.length ∧
      argc < expTgtIdx + tgts.length ∧
      argc < srcIdx + srcs.length ∧
      srcs.all isSupportedScalarOrUnitTy = true ∧
      tgts.all isSupportedScalarOrUnitTy = true ∧
      (∀ i, i < srcs.length → srcIdx + i ≤ argc → isLiveLocal bs i = true ∧ mapLocal ms i = srcIdx + i) ∧
      (∀ i, isLiveLocal bs i = true →
        expTgtIdx ≤ mapLocal ms i ∧
        mapLocal ms i < expTgtIdx + tgts.length ∧
        Trusted.MirSemantics.getElem? tgts (mapLocal ms i - expTgtIdx) = Trusted.MirSemantics.getElem? srcs i) ∧
      (∀ i j, isLiveLocal bs i = true → isLiveLocal bs j = true → mapLocal ms i = mapLocal ms j → i = j)
  | argc, srcIdx, expTgtIdx, [], [], [], [], hOk, _ => by
    unfold checkZipLocals at hOk
    cases h1 : Nat.blt argc expTgtIdx with
    | false => rw [h1] at hOk; cases hOk
    | true =>
      rw [h1] at hOk
      dsimp only [List.length]
      rw [Nat.add_zero, Nat.add_zero]
      refine ⟨rfl, nat_blt_true_iff.mp h1, nat_blt_true_iff.mp hOk, rfl, rfl, ?_, ?_, ?_⟩
      · intro _ hi _; exact False.elim (Nat.not_lt_zero _ hi)
      · intro _ hi; unfold isLiveLocal at hi; cases hi
      · intro _ _ hi _ _; unfold isLiveLocal at hi; cases hi
  | _, _, _, [], [], [], _ :: _, hOk, _ => by cases hOk
  | _, _, _, [], [], _ :: _, _, hOk, _ => by cases hOk
  | _, _, _, [], _ :: _, [], _, hOk, _ => by cases hOk
  | _, _, _, [], _ :: _, _ :: _, _, hOk, _ => by cases hOk
  | _, _, _, _ :: _, [], [], _, hOk, _ => by cases hOk
  | _, _, _, _ :: _, [], _ :: _, _, hOk, _ => by cases hOk
  | _, _, _, _ :: _, _ :: _, [], _, hOk, _ => by cases hOk
  | argc, srcIdx, expTgtIdx, ty :: srcs, b :: bs, m :: ms, tgts, hOk, hAbi => by
    unfold checkZipLocals at hOk
    cases hStep : checkZipStep argc srcIdx expTgtIdx ty b m tgts with
    | none => rw [hStep] at hOk; cases hOk
    | some nextPair =>
      rw [hStep] at hOk
      dsimp only at hOk
      unfold checkZipStep at hStep
      cases hSup : isSupportedScalarOrUnitTy ty with
      | false =>
        rw [hSup] at hStep
        cases hStep
      | true =>
        rw [hSup] at hStep
        dsimp only at hStep
        cases hNeedAbi : Nat.ble srcIdx argc && !b with
        | true =>
          rw [hNeedAbi] at hStep
          cases hStep
        | false =>
          rw [hNeedAbi] at hStep
          dsimp only at hStep
          cases b with
          | false =>
            dsimp only at hStep
            injection hStep with hPairEq
            subst hPairEq
            have hNextAbi : srcIdx + 1 ≤ argc → expTgtIdx = srcIdx + 1 := by
              intro hLe
              have hSrcLe : srcIdx ≤ argc := Nat.le_of_lt hLe
              have hBle : Nat.ble srcIdx argc = true := nat_ble_true_iff.mpr hSrcLe
              rw [hBle] at hNeedAbi
              cases hNeedAbi
            let ⟨ihLen, ihTgtLt, ihSrcLt, ihSrcSup, ihTgtSup, ihAbi, ihLive, ihInj⟩ :=
              checkZipLocals_sound argc (srcIdx + 1) expTgtIdx srcs bs ms tgts hOk hNextAbi
            have hSrcSucc : srcIdx + (srcs.length + 1) = (srcIdx + 1) + srcs.length := by
              rw [Nat.add_assoc, Nat.add_comm 1 srcs.length]
            refine ⟨congrArg Nat.succ ihLen, ihTgtLt, ?_, ?_, ihTgtSup, ?_, ?_, ?_⟩
            · change argc < srcIdx + (srcs.length + 1)
              rw [hSrcSucc]; exact ihSrcLt
            · change (isSupportedScalarOrUnitTy ty && srcs.all isSupportedScalarOrUnitTy) = true
              rw [hSup, ihSrcSup]; rfl
            · intro i hi hLe
              cases i with
              | zero =>
                rw [Nat.add_zero] at hLe
                have hBle : Nat.ble srcIdx argc = true := nat_ble_true_iff.mpr hLe
                rw [hBle] at hNeedAbi; cases hNeedAbi
              | succ k =>
                have hkLe : (srcIdx + 1) + k ≤ argc := by
                  rw [← add_succ_right_comm srcIdx k]
                  exact hLe
                have hRes := ihAbi k (Nat.lt_of_succ_lt_succ hi) hkLe
                change isLiveLocal bs k = true ∧ mapLocal ms k = srcIdx + (k + 1)
                rw [add_succ_right_comm srcIdx k]
                exact hRes
            · intro i hi
              cases i with
              | zero => cases hi
              | succ k => exact ihLive k hi
            · intro i j hi hj hMap
              cases i with
              | zero => cases hi
              | succ i' =>
                cases j with
                | zero => cases hj
                | succ j' => exact congrArg Nat.succ (ihInj i' j' hi hj hMap)
          | true =>
            dsimp only at hStep
            cases hM : Nat.beq m expTgtIdx with
            | false =>
              rw [hM] at hStep
              cases hStep
            | true =>
              rw [hM] at hStep
              dsimp only at hStep
              have hmEq : m = expTgtIdx := nat_beq_eq hM
              subst hmEq
              cases tgts with
              | nil => cases hStep
              | cons tgtTy tgtsRest =>
                dsimp only at hStep
                cases hTyEqBool : MirTy.beq ty tgtTy with
                | false =>
                  rw [hTyEqBool] at hStep
                  cases hStep
                | true =>
                  rw [hTyEqBool] at hStep
                  dsimp only at hStep
                  injection hStep with hPairEq
                  subst hPairEq
                  have hTyEq : ty = tgtTy := mirTy_beq_eq hTyEqBool
                  subst hTyEq
                  have hNextAbi : srcIdx + 1 ≤ argc → m + 1 = srcIdx + 1 := by
                    intro hLe
                    rw [hAbi (Nat.le_of_lt hLe)]
                  let ⟨ihLen, ihTgtLt, ihSrcLt, ihSrcSup, ihTgtSup, ihAbi, ihLive, ihInj⟩ :=
                    checkZipLocals_sound argc (srcIdx + 1) (m + 1) srcs bs ms tgtsRest hOk hNextAbi
                  have hTgtSucc : m + (tgtsRest.length + 1) = (m + 1) + tgtsRest.length := by
                    rw [Nat.add_assoc, Nat.add_comm 1 tgtsRest.length]
                  have hSrcSucc : srcIdx + (srcs.length + 1) = (srcIdx + 1) + srcs.length := by
                    rw [Nat.add_assoc, Nat.add_comm 1 srcs.length]
                  refine ⟨congrArg Nat.succ ihLen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · change argc < m + (tgtsRest.length + 1)
                    rw [hTgtSucc]; exact ihTgtLt
                  · change argc < srcIdx + (srcs.length + 1)
                    rw [hSrcSucc]; exact ihSrcLt
                  · change (isSupportedScalarOrUnitTy ty && srcs.all isSupportedScalarOrUnitTy) = true
                    rw [hSup, ihSrcSup]; rfl
                  · change (isSupportedScalarOrUnitTy ty && tgtsRest.all isSupportedScalarOrUnitTy) = true
                    rw [hSup, ihTgtSup]; rfl
                  · intro i hi hLe
                    cases i with
                    | zero =>
                      rw [Nat.add_zero] at hLe
                      refine ⟨rfl, ?_⟩
                      change m = srcIdx + 0
                      rw [Nat.add_zero]
                      exact hAbi hLe
                    | succ k =>
                      have hkLe : (srcIdx + 1) + k ≤ argc := by
                        rw [← add_succ_right_comm srcIdx k]
                        exact hLe
                      have ihRes := ihAbi k (Nat.lt_of_succ_lt_succ hi) hkLe
                      change isLiveLocal bs k = true ∧ mapLocal ms k = srcIdx + (k + 1)
                      rw [add_succ_right_comm srcIdx k]
                      exact ihRes
                  · intro i hi
                    cases i with
                    | zero =>
                      refine ⟨Nat.le_refl _, ?_, ?_⟩
                      · change m < m + (tgtsRest.length + 1)
                        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
                      · change Trusted.MirSemantics.getElem? (ty :: tgtsRest) (m - m) = Trusted.MirSemantics.getElem? (ty :: srcs) 0
                        rw [Nat.sub_self m]; rfl
                    | succ k =>
                      let ⟨hkGe, hkLt, hkGet⟩ := ihLive k hi
                      refine ⟨Nat.le_of_lt hkGe, ?_, ?_⟩
                      · change mapLocal ms k < m + (tgtsRest.length + 1)
                        rw [hTgtSucc]; exact hkLt
                      · change Trusted.MirSemantics.getElem? (ty :: tgtsRest) (mapLocal ms k - m) = Trusted.MirSemantics.getElem? (ty :: srcs) (k + 1)
                        rw [sub_succ_eq_sub_add_one hkGe]
                        exact hkGet
                  · intro i j hi hj hMap
                    cases i with
                    | zero =>
                      cases j with
                      | zero => rfl
                      | succ j' =>
                        let ⟨hjGe, _, _⟩ := ihLive j' hj
                        change m = mapLocal ms j' at hMap
                        rw [← hMap] at hjGe
                        exact False.elim (Nat.not_succ_le_self m hjGe)
                    | succ i' =>
                      cases j with
                      | zero =>
                        let ⟨hiGe, _, _⟩ := ihLive i' hi
                        change mapLocal ms i' = m at hMap
                        rw [hMap] at hiGe
                        exact False.elim (Nat.not_succ_le_self m hiGe)
                      | succ j' =>
                        exact congrArg Nat.succ (ihInj i' j' hi hj hMap)

noncomputable def operandLocalsInMaskTree (tree : MaskTree) : Operand → Bool
  | .copy p | .move p => maskTreeGet tree p.localId
  | .constant _ => true

noncomputable def operandListLocalsInMaskTree (tree : MaskTree) : List Operand → Bool
  | [] => true
  | op :: ops => operandLocalsInMaskTree tree op && operandListLocalsInMaskTree tree ops

noncomputable def rvalueLocalsInMaskTree (tree : MaskTree) : Rvalue → Bool
  | .use op => operandLocalsInMaskTree tree op
  | .binaryOp _ l r => operandLocalsInMaskTree tree l && operandLocalsInMaskTree tree r
  | .unaryOp _ x => operandLocalsInMaskTree tree x
  | .discriminant p | .ref _ p | .addressOf _ p => maskTreeGet tree p.localId
  | .aggregateTuple fs => operandListLocalsInMaskTree tree fs
  | .unsupported => true

noncomputable def stmtTreeCheck (tree : MaskTree) (numLocals : Nat) : StatementKind → Bool
  | .assign dst rv => maskTreeGet tree dst.localId && rvalueLocalsInMaskTree tree rv
  | .storageLive id => Nat.blt id numLocals && !(maskTreeGet tree id)
  | .storageDead id => !Nat.beq id 0 && Nat.blt id numLocals && !(maskTreeGet tree id)
  | .nop | .unsupported => true

noncomputable def termTreeCheck (tree : MaskTree) : TerminatorKind → Bool
  | .switchInt discr _ => operandLocalsInMaskTree tree discr
  | .assert cond _ _ _ _ => operandLocalsInMaskTree tree cond
  | .call _ args dst _ _ => operandListLocalsInMaskTree tree args && maskTreeGet tree dst.localId
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true

noncomputable def checkStmtsTreeSeq (tree : MaskTree) (numLocals : Nat) : List StatementKind → Bool
  | [] => true
  | s :: ss => stmtTreeCheck tree numLocals s && checkStmtsTreeSeq tree numLocals ss

noncomputable def checkStmtsTree8 (tree : MaskTree) (numLocals : Nat) : List StatementKind → Bool
  | s0::s1::s2::s3::s4::s5::s6::s7::ss =>
    stmtTreeCheck tree numLocals s0 &&
    (stmtTreeCheck tree numLocals s1 &&
    (stmtTreeCheck tree numLocals s2 &&
    (stmtTreeCheck tree numLocals s3 &&
    (stmtTreeCheck tree numLocals s4 &&
    (stmtTreeCheck tree numLocals s5 &&
    (stmtTreeCheck tree numLocals s6 &&
    (stmtTreeCheck tree numLocals s7 &&
    checkStmtsTree8 tree numLocals ss)))))))
  | ss => checkStmtsTreeSeq tree numLocals ss

private theorem checkStmtsTree8_eq (tree : MaskTree) (numLocals : Nat) :
    ∀ ss : List StatementKind, checkStmtsTree8 tree numLocals ss = checkStmtsTreeSeq tree numLocals ss
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _]
  | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] => rfl
  | s0::s1::s2::s3::s4::s5::s6::s7::ss => by
    unfold checkStmtsTree8
    rw [checkStmtsTree8_eq tree numLocals ss]
    rfl

noncomputable def checkBlocksTreeSeq (tree : MaskTree) (numLocals : Nat) : List BasicBlock → Bool
  | [] => true
  | bb :: bbs =>
    checkStmtsTreeSeq tree numLocals bb.statements &&
    termTreeCheck tree bb.terminator &&
    checkBlocksTreeSeq tree numLocals bbs

noncomputable def checkBlocksTree8 (tree : MaskTree) (numLocals : Nat) : List BasicBlock → Bool
  | [] => true
  | bb :: bbs =>
    checkStmtsTree8 tree numLocals bb.statements &&
    termTreeCheck tree bb.terminator &&
    checkBlocksTree8 tree numLocals bbs

noncomputable def checkZipLocalsCount (argc srcIdx expTgtIdx : Nat) :
    List MirTy → List Bool → List Nat → List MirTy → Option Nat
  | [], [], [], [] => if Nat.blt argc expTgtIdx && Nat.blt argc srcIdx then some srcIdx else none
  | ty :: tys, b :: bs, m :: ms, tgts =>
    match checkZipStep argc srcIdx expTgtIdx ty b m tgts with
    | none => none
    | some (nextTgt, tgtsRest) =>
      checkZipLocalsCount argc (srcIdx + 1) nextTgt tys bs ms tgtsRest
  | _, _, _, _ => none

noncomputable def checkZipLocals8Count (argc srcIdx expTgtIdx : Nat) :
    List MirTy → List Bool → List Nat → List MirTy → Option Nat
  | s0::s1::s2::s3::s4::s5::s6::s7::tys,
    b0::b1::b2::b3::b4::b5::b6::b7::bs,
    m0::m1::m2::m3::m4::m5::m6::m7::ms, tgts =>
    match checkZipStep argc srcIdx expTgtIdx s0 b0 m0 tgts with
    | none => none
    | some (e1, t1) =>
      match checkZipStep argc (srcIdx + 1) e1 s1 b1 m1 t1 with
      | none => none
      | some (e2, t2) =>
        match checkZipStep argc (srcIdx + 2) e2 s2 b2 m2 t2 with
        | none => none
        | some (e3, t3) =>
          match checkZipStep argc (srcIdx + 3) e3 s3 b3 m3 t3 with
          | none => none
          | some (e4, t4) =>
            match checkZipStep argc (srcIdx + 4) e4 s4 b4 m4 t4 with
            | none => none
            | some (e5, t5) =>
              match checkZipStep argc (srcIdx + 5) e5 s5 b5 m5 t5 with
              | none => none
              | some (e6, t6) =>
                match checkZipStep argc (srcIdx + 6) e6 s6 b6 m6 t6 with
                | none => none
                | some (e7, t7) =>
                  match checkZipStep argc (srcIdx + 7) e7 s7 b7 m7 t7 with
                  | none => none
                  | some (e8, t8) =>
                    checkZipLocals8Count argc (srcIdx + 8) e8 tys bs ms t8
  | tys, bs, ms, tgts => checkZipLocalsCount argc srcIdx expTgtIdx tys bs ms tgts

private theorem checkZipLocals8Count_eq :
    ∀ (argc srcIdx expTgtIdx : Nat) (tys : List MirTy) (bs : List Bool) (ms : List Nat) (tgts : List MirTy),
      checkZipLocals8Count argc srcIdx expTgtIdx tys bs ms tgts =
      checkZipLocalsCount argc srcIdx expTgtIdx tys bs ms tgts
  | _, _, _, [], _, _, _ | _, _, _, [_], _, _, _ | _, _, _, [_, _], _, _, _
  | _, _, _, [_, _, _], _, _, _ | _, _, _, [_, _, _, _], _, _, _
  | _, _, _, [_, _, _, _, _], _, _, _ | _, _, _, [_, _, _, _, _, _], _, _, _
  | _, _, _, [_, _, _, _, _, _, _], _, _, _ => rfl
  | _, _, _, _::_::_::_::_::_::_::_::_, [], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _], _, _
  | _, _, _, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _, _], _, _ => rfl
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _], _
  | _, _, _, _::_::_::_::_::_::_::_::_, _::_::_::_::_::_::_::_::_, [_, _, _, _, _, _, _], _ => rfl
  | argc, srcIdx, expTgtIdx,
    s0::s1::s2::s3::s4::s5::s6::s7::tys,
    b0::b1::b2::b3::b4::b5::b6::b7::bs,
    m0::m1::m2::m3::m4::m5::m6::m7::ms, tgts => by
    unfold checkZipLocals8Count
    cases h0 : checkZipStep argc srcIdx expTgtIdx s0 b0 m0 tgts with
    | none => unfold checkZipLocalsCount; rw [h0]
    | some p1 =>
      rw [checkZipLocalsCount.eq_2, h0]; dsimp only
      cases h1 : checkZipStep argc (srcIdx + 1) p1.1 s1 b1 m1 p1.2 with
      | none => unfold checkZipLocalsCount; rw [h1]
      | some p2 =>
        rw [checkZipLocalsCount.eq_2, h1]; dsimp only
        cases h2 : checkZipStep argc (srcIdx + 2) p2.1 s2 b2 m2 p2.2 with
        | none => unfold checkZipLocalsCount; rw [h2]
        | some p3 =>
          rw [checkZipLocalsCount.eq_2, h2]; dsimp only
          cases h3 : checkZipStep argc (srcIdx + 3) p3.1 s3 b3 m3 p3.2 with
          | none => unfold checkZipLocalsCount; rw [h3]
          | some p4 =>
            rw [checkZipLocalsCount.eq_2, h3]; dsimp only
            cases h4 : checkZipStep argc (srcIdx + 4) p4.1 s4 b4 m4 p4.2 with
            | none => unfold checkZipLocalsCount; rw [h4]
            | some p5 =>
              rw [checkZipLocalsCount.eq_2, h4]; dsimp only
              cases h5 : checkZipStep argc (srcIdx + 5) p5.1 s5 b5 m5 p5.2 with
              | none => unfold checkZipLocalsCount; rw [h5]
              | some p6 =>
                rw [checkZipLocalsCount.eq_2, h5]; dsimp only
                cases h6 : checkZipStep argc (srcIdx + 6) p6.1 s6 b6 m6 p6.2 with
                | none => unfold checkZipLocalsCount; rw [h6]
                | some p7 =>
                  rw [checkZipLocalsCount.eq_2, h6]; dsimp only
                  cases h7 : checkZipStep argc (srcIdx + 7) p7.1 s7 b7 m7 p7.2 with
                  | none => unfold checkZipLocalsCount; rw [h7]
                  | some p8 =>
                    rw [checkZipLocalsCount.eq_2, h7]; dsimp only
                    exact checkZipLocals8Count_eq argc (srcIdx + 8) p8.1 tys bs ms p8.2

private theorem checkZipLocalsCount_spec :
    ∀ (argc srcIdx expTgtIdx n : Nat) (srcs : List MirTy) (bs : List Bool) (ms : List Nat) (tgts : List MirTy),
      checkZipLocalsCount argc srcIdx expTgtIdx srcs bs ms tgts = some n →
      checkZipLocals argc srcIdx expTgtIdx srcs bs ms tgts = true ∧ n = srcIdx + srcs.length
  | argc, srcIdx, expTgtIdx, n, [], [], [], [], hOk => by
    unfold checkZipLocalsCount at hOk
    unfold checkZipLocals
    cases hB : Nat.blt argc expTgtIdx && Nat.blt argc srcIdx with
    | false => rw [hB] at hOk; cases hOk
    | true =>
      rw [hB] at hOk
      injection hOk with hEq
      subst hEq
      dsimp only [List.length]
      rw [Nat.add_zero]
      exact ⟨rfl, rfl⟩
  | _, _, _, _, [], [], [], _ :: _, hOk => by cases hOk
  | _, _, _, _, [], [], _ :: _, _, hOk => by cases hOk
  | _, _, _, _, [], _ :: _, [], _, hOk => by cases hOk
  | _, _, _, _, [], _ :: _, _ :: _, _, hOk => by cases hOk
  | _, _, _, _, _ :: _, [], [], _, hOk => by cases hOk
  | _, _, _, _, _ :: _, [], _ :: _, _, hOk => by cases hOk
  | _, _, _, _, _ :: _, _ :: _, [], _, hOk => by cases hOk
  | argc, srcIdx, expTgtIdx, n, ty :: srcs, b :: bs, m :: ms, tgts, hOk => by
    unfold checkZipLocalsCount at hOk
    cases hStep : checkZipStep argc srcIdx expTgtIdx ty b m tgts with
    | none => rw [hStep] at hOk; cases hOk
    | some nextPair =>
      rw [hStep] at hOk; dsimp only at hOk
      let ⟨hRecBool, hRecLen⟩ := checkZipLocalsCount_spec argc (srcIdx + 1) nextPair.1 n srcs bs ms nextPair.2 hOk
      unfold checkZipLocals
      rw [hStep]; dsimp only
      refine ⟨hRecBool, ?_⟩
      change n = srcIdx + (srcs.length + 1)
      rw [Nat.add_assoc, Nat.add_comm 1 srcs.length] at hRecLen
      exact hRecLen

/-- Unbatched positional `MaskTree` compaction checker (exhibits `maxRecDepth` cliff near `S = 385`). -/
noncomputable def checkR3Positional (bSrc : Body) (spec : CompactionSpec) : Bool :=
  match checkZipLocalsCount bSrc.argumentCount 0 0 bSrc.locals spec.liveMask spec.slotMap spec.targetLocals with
  | none => false
  | some numLocals => checkBlocksTreeSeq (buildMaskTree spec.liveMask) numLocals bSrc.basicBlocks

/-- Fast `O(L + S log L)` batched positional `MaskTree` + stride-8 compaction checker. -/
noncomputable def checkR3PositionalBatched (bSrc : Body) (spec : CompactionSpec) : Bool :=
  match checkZipLocals8Count bSrc.argumentCount 0 0 bSrc.locals spec.liveMask spec.slotMap spec.targetLocals with
  | none => false
  | some numLocals => checkBlocksTree8 (buildMaskTree spec.liveMask) numLocals bSrc.basicBlocks

private theorem checkBlocksTree8_eq (tree : MaskTree) (numLocals : Nat) :
    ∀ bbs : List BasicBlock,
      checkBlocksTree8 tree numLocals bbs = checkBlocksTreeSeq tree numLocals bbs
  | [] => rfl
  | bb :: bbs => by
    unfold checkBlocksTree8 checkBlocksTreeSeq
    rw [checkStmtsTree8_eq, checkBlocksTree8_eq tree numLocals bbs]

/-- Exact observational equivalence between stride-8 batched and unbatched positional checkers. -/
theorem checkR3PositionalBatched_eq (bSrc : Body) (spec : CompactionSpec) :
    checkR3PositionalBatched bSrc spec = checkR3Positional bSrc spec := by
  unfold checkR3PositionalBatched checkR3Positional
  rw [checkZipLocals8Count_eq]
  cases checkZipLocalsCount bSrc.argumentCount 0 0 bSrc.locals spec.liveMask spec.slotMap spec.targetLocals with
  | none => rfl
  | some numLocals => exact checkBlocksTree8_eq (buildMaskTree spec.liveMask) numLocals bSrc.basicBlocks

private theorem operandListLocalsInMaskTree_eq (mask : List Bool) :
    ∀ ops : List Operand, operandListLocalsInMaskTree (buildMaskTree mask) ops = operandListLocalsInMask mask ops
  | [] => rfl
  | op :: ops => by
    change (operandLocalsInMaskTree (buildMaskTree mask) op && operandListLocalsInMaskTree (buildMaskTree mask) ops) =
      (operandLocalsInMask mask op && operandListLocalsInMask mask ops)
    have hop : operandLocalsInMaskTree (buildMaskTree mask) op = operandLocalsInMask mask op := by
      cases op with | constant _ => rfl | copy p | move p => unfold operandLocalsInMaskTree operandLocalsInMask; dsimp only; rw [maskTreeGet_buildMaskTree]
    rw [hop, operandListLocalsInMaskTree_eq mask ops]

private theorem stmtTreeCheck_sound {mask : List Bool} {numLocals : Nat} {s : StatementKind}
    (h : stmtTreeCheck (buildMaskTree mask) numLocals s = true) :
    stmtRefLocalsInMask mask s = true ∧ stmtStorageOnlyOnDead mask numLocals s = true := by
  cases s with
  | nop | unsupported => exact ⟨rfl, rfl⟩
  | storageLive id =>
    unfold stmtTreeCheck at h; dsimp only at h
    unfold stmtRefLocalsInMask stmtStorageOnlyOnDead
    rw [maskTreeGet_buildMaskTree] at h
    exact ⟨rfl, h⟩
  | storageDead id =>
    unfold stmtTreeCheck at h; dsimp only at h
    unfold stmtRefLocalsInMask stmtStorageOnlyOnDead
    rw [maskTreeGet_buildMaskTree] at h
    exact ⟨rfl, h⟩
  | assign dst rv =>
    unfold stmtTreeCheck at h; dsimp only at h
    unfold stmtRefLocalsInMask stmtStorageOnlyOnDead
    have hRvEq : rvalueLocalsInMaskTree (buildMaskTree mask) rv = rvalueLocalsInMask mask rv := by
      cases rv with
      | use op =>
        unfold rvalueLocalsInMaskTree rvalueLocalsInMask; dsimp only
        cases op with
        | constant _ => rfl
        | copy p | move p => unfold operandLocalsInMaskTree operandLocalsInMask; dsimp only; rw [maskTreeGet_buildMaskTree]
      | binaryOp _ l r =>
        unfold rvalueLocalsInMaskTree rvalueLocalsInMask; dsimp only
        have hl : operandLocalsInMaskTree (buildMaskTree mask) l = operandLocalsInMask mask l := by
          cases l with | constant _ => rfl | copy p | move p => unfold operandLocalsInMaskTree operandLocalsInMask; dsimp only; rw [maskTreeGet_buildMaskTree]
        have hr : operandLocalsInMaskTree (buildMaskTree mask) r = operandLocalsInMask mask r := by
          cases r with | constant _ => rfl | copy p | move p => unfold operandLocalsInMaskTree operandLocalsInMask; dsimp only; rw [maskTreeGet_buildMaskTree]
        rw [hl, hr]
      | unaryOp _ x =>
        unfold rvalueLocalsInMaskTree rvalueLocalsInMask; dsimp only
        cases x with | constant _ => rfl | copy p | move p => unfold operandLocalsInMaskTree operandLocalsInMask; dsimp only; rw [maskTreeGet_buildMaskTree]
      | discriminant p | ref _ p | addressOf _ p =>
        unfold rvalueLocalsInMaskTree rvalueLocalsInMask; dsimp only
        rw [maskTreeGet_buildMaskTree]
      | aggregateTuple fs =>
        unfold rvalueLocalsInMaskTree rvalueLocalsInMask; dsimp only
        exact operandListLocalsInMaskTree_eq mask fs
      | unsupported => rfl
    rw [maskTreeGet_buildMaskTree, hRvEq] at h
    exact ⟨h, rfl⟩

private theorem checkStmtsTreeSeq_sound (mask : List Bool) (numLocals : Nat) :
    ∀ stms : List StatementKind,
      checkStmtsTreeSeq (buildMaskTree mask) numLocals stms = true →
      stms.all (stmtRefLocalsInMask mask) = true ∧ stms.all (stmtStorageOnlyOnDead mask numLocals) = true
  | [] => fun _ => ⟨rfl, rfl⟩
  | s :: ss => fun hSt => by
    unfold checkStmtsTreeSeq at hSt
    cases hs1 : stmtTreeCheck (buildMaskTree mask) numLocals s with
    | false => rw [hs1] at hSt; cases hSt
    | true =>
      rw [hs1] at hSt
      let ⟨ihs1, ihs2⟩ := checkStmtsTreeSeq_sound mask numLocals ss hSt
      let ⟨hRefS, hDeadS⟩ := stmtTreeCheck_sound hs1
      refine ⟨?_, ?_⟩
      · change (stmtRefLocalsInMask mask s && ss.all (stmtRefLocalsInMask mask)) = true
        rw [hRefS, ihs1]; rfl
      · change (stmtStorageOnlyOnDead mask numLocals s && ss.all (stmtStorageOnlyOnDead mask numLocals)) = true
        rw [hDeadS, ihs2]; rfl

private theorem checkBlocksTreeSeq_sound {mask : List Bool} {numLocals : Nat} {bbs : List BasicBlock}
    (h : checkBlocksTreeSeq (buildMaskTree mask) numLocals bbs = true) :
    bbs.all (fun bb =>
      bb.statements.all (stmtRefLocalsInMask mask) &&
      termLocalsInMask mask bb.terminator) = true ∧
    bbs.all (fun bb => bb.statements.all (stmtStorageOnlyOnDead mask numLocals)) = true := by
  induction bbs with
  | nil => exact ⟨rfl, rfl⟩
  | cons bb bbs ih =>
    unfold checkBlocksTreeSeq at h
    cases hSt : checkStmtsTreeSeq (buildMaskTree mask) numLocals bb.statements with
    | false => rw [hSt] at h; cases h
    | true =>
      rw [hSt] at h
      cases hTm : termTreeCheck (buildMaskTree mask) bb.terminator with
      | false => rw [hTm] at h; cases h
      | true =>
        rw [hTm] at h
        let ⟨ihRef, ihDead⟩ := ih h
        have hStPair := checkStmtsTreeSeq_sound mask numLocals bb.statements hSt
        have hTmEq : termLocalsInMask mask bb.terminator = true := by
          cases hTerm : bb.terminator with
          | goto _ | return_ | unreachable | unwindResume | unsupported => rfl
          | switchInt d _ =>
            rw [hTerm] at hTm
            unfold termTreeCheck at hTm; dsimp only at hTm
            unfold termLocalsInMask
            cases d with
            | constant _ => rfl
            | copy p | move p => unfold operandLocalsInMaskTree at hTm; unfold operandLocalsInMask; dsimp only at hTm; dsimp only; rw [maskTreeGet_buildMaskTree] at hTm; exact hTm
          | assert c _ _ _ _ =>
            rw [hTerm] at hTm
            unfold termTreeCheck at hTm; dsimp only at hTm
            unfold termLocalsInMask
            cases c with
            | constant _ => rfl
            | copy p | move p => unfold operandLocalsInMaskTree at hTm; unfold operandLocalsInMask; dsimp only at hTm; dsimp only; rw [maskTreeGet_buildMaskTree] at hTm; exact hTm
          | call _ args dst _ _ =>
            rw [hTerm] at hTm
            unfold termTreeCheck at hTm; dsimp only at hTm
            unfold termLocalsInMask
            have hListEq := operandListLocalsInMaskTree_eq mask args
            rw [hListEq, maskTreeGet_buildMaskTree] at hTm
            exact hTm
        refine ⟨?_, ?_⟩
        · change ((bb.statements.all (stmtRefLocalsInMask mask) && termLocalsInMask mask bb.terminator) &&
            bbs.all (fun bb => bb.statements.all (stmtRefLocalsInMask mask) && termLocalsInMask mask bb.terminator)) = true
          rw [hStPair.1, hTmEq, ihRef]; rfl
        · change (bb.statements.all (stmtStorageOnlyOnDead mask numLocals) &&
            bbs.all (fun bb => bb.statements.all (stmtStorageOnlyOnDead mask numLocals))) = true
          rw [hStPair.2, ihDead]; rfl

/-- End-to-end kernel soundness of `checkR3PositionalBatched`: proving the `O(L + S log L)`
stride-8 positional check yields `ValidBodyCompaction bSrc spec`, hence full
bidirectional `compact_preserves_eval_iff` and `wpProg_transport_compact_iff`. -/
theorem validBodyCompaction_of_checkR3PositionalBatched {bSrc : Body} {spec : CompactionSpec}
    (h : checkR3PositionalBatched bSrc spec = true) : ValidBodyCompaction bSrc spec := by
  rw [checkR3PositionalBatched_eq] at h
  unfold checkR3Positional at h
  cases hZipCnt : checkZipLocalsCount bSrc.argumentCount 0 0 bSrc.locals spec.liveMask spec.slotMap spec.targetLocals with
  | none => rw [hZipCnt] at h; cases h
  | some numLocals =>
    rw [hZipCnt] at h
    dsimp only at h
    let ⟨hZip, hLenNum⟩ := checkZipLocalsCount_spec bSrc.argumentCount 0 0 numLocals bSrc.locals spec.liveMask spec.slotMap spec.targetLocals hZipCnt
    rw [Nat.zero_add] at hLenNum
    subst hLenNum
    let ⟨hLenEq, hTgtLt, hSrcLt, hSrcSup, hTgtSup, hAbi, hLive, hInj⟩ :=
      checkZipLocals_sound bSrc.argumentCount 0 0 bSrc.locals spec.liveMask spec.slotMap spec.targetLocals
        hZip (fun _ => rfl)
    rw [Nat.zero_add] at hTgtLt hSrcLt
    let ⟨hRef, hDead⟩ := checkBlocksTreeSeq_sound h
    refine ⟨?_, hInj, ?_, hRef, hDead⟩
    · refine ⟨by rw [hLenEq]; exact hSrcLt, ?_⟩
      intro i hiLe
      have hiLt : i < bSrc.locals.length := Nat.lt_of_le_of_lt hiLe hSrcLt
      have hRes := hAbi i hiLt (by rw [Nat.zero_add]; exact hiLe)
      rw [Nat.zero_add] at hRes
      exact hRes
    · refine ⟨hLenEq, hTgtLt, hTgtSup, hSrcSup, ?_⟩
      intro i hiLive
      let ⟨_, hmLt, hmGet⟩ := hLive i hiLive
      rw [Nat.zero_add] at hmLt
      rw [Nat.sub_zero] at hmGet
      exact ⟨hmLt, hmGet⟩

/-!
## Part V: Sharpness Counterexamples and Certified Positive Witness
-/

private theorem behavior_unique_of_exec {p : Program} {q : Query} {s0 : State}
    {outActual out : TerminalOut} {fuel : Nat}
    (hInit : initState p q = .ok s0)
    (hExec : execOutcomeState p (fun o => o = outActual) (fun _ => False) fuel s0)
    (hBeh : Behavior p q out) : out = outActual := by
  unfold Behavior ReachesResult at hBeh
  rw [hInit] at hBeh
  let ⟨s, hReach, hDone⟩ := hBeh
  let ⟨f', hExecS⟩ := reaches_execOutcomeState hReach hExec
  cases f' with
  | zero => exact False.elim hExecS
  | succ f'' =>
    let ⟨c, hc, hEval⟩ := hDone
    change c = 0 at hc; subst hc
    change match evalStep p 0 s with
      | .step st' => execOutcomeState p (fun o => o = outActual) (fun _ => False) f'' st'
      | .done out => out = outActual
      | .fault _ => False at hExecS
    rw [hEval] at hExecS
    exact hExecS

private theorem not_behavior_of_execFault {p : Program} {q : Query} {s0 : State}
    {fuel : Nat}
    (hInit : initState p q = .ok s0)
    (hExec : execOutcomeState p (fun _ => False) (fun _ => True) fuel s0)
    (out : TerminalOut) : ¬ Behavior p q out := by
  intro hBeh
  unfold Behavior ReachesResult at hBeh
  rw [hInit] at hBeh
  let ⟨s, hReach, hDone⟩ := hBeh
  let ⟨f', hExecS⟩ := reaches_execOutcomeState hReach hExec
  cases f' with
  | zero => exact False.elim hExecS
  | succ f'' =>
    let ⟨c, hc, hEval⟩ := hDone
    change c = 0 at hc; subst hc
    change match evalStep p 0 s with
      | .step st' => execOutcomeState p (fun _ => False) (fun _ => True) f'' st'
      | .done _ => False
      | .fault _ => True at hExecS
    rw [hEval] at hExecS
    exact False.elim hExecS

/-- Positive certified witness demonstrating `checkR3PositionalBatched` ->
`ValidBodyCompaction` -> `compact_preserves_eval_iff`. -/
noncomputable def posSrcBody : Body :=
  { argumentCount := 1
    locals := [.bool, .bool, .bool, .bool]
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .storageDead 2,
        .assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))
      ]
      terminator := .return_
    }] }

noncomputable def posSpec : CompactionSpec :=
  { liveMask := [true, true, false, true]
    slotMap := [0, 1, 0, 2]
    targetLocals := [.bool, .bool, .bool] }

theorem pos_witness_valid : ValidBodyCompaction posSrcBody posSpec :=
  validBodyCompaction_of_checkR3PositionalBatched (by rfl)

theorem pos_witness_behavior_iff :
    Behavior { bodies := [posSrcBody], entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 1 }
        { args := [.bool true] } (.returned ⟨.bool true, ⟨[]⟩⟩) ↔
    Behavior (compactProgram [posSpec] { bodies := [posSrcBody], entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 1 })
        { args := [.bool true] } (.returned ⟨.bool true, ⟨[]⟩⟩) := by
  have hProg : ValidProgramCompaction [posSpec]
      { bodies := [posSrcBody], entryDefId := 0, pointerWidthBits := 64, mirProfileVersion := 1 } := by
    refine ⟨rfl, ?_⟩
    intro d b sp hb hsp
    cases d with
    | zero =>
      injection hb with hbEq; subst hbEq
      injection hsp with hspEq; subst hspEq
      exact pos_witness_valid
    | succ d' => cases hb
  exact behavior_compact_iff hProg _ _

/-- **CE1 (Non-injective `slotMap` breaks operational equivalence):**
Mapping two distinct live locals `1 ≠ 2` to the same target slot `1` satisfies
`PreservesAbiSlots`, `ValidTargetTypes`, `AllReferencedLocalsInLiveMask`, and
`StorageMarkersOnlyOnDead`, while violating `InjectiveOnLive` and silently
overwriting `false` with `true`. -/
noncomputable def ce1Body : Body :=
  { argumentCount := 0
    locals := [.bool, .bool, .bool]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨2, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }] }

noncomputable def ce1Spec : CompactionSpec :=
  { liveMask := [true, true, true]
    slotMap := [0, 1, 1]
    targetLocals := [.bool, .bool] }

noncomputable def ce1SrcProg : Program :=
  { bodies := [ce1Body], pointerWidthBits := 64, mirProfileVersion := 1 }

noncomputable def ce1TgtProg : Program :=
  compactProgram [ce1Spec] ce1SrcProg

theorem ce1_non_injective_renumbering_breaks_eval :
    PreservesAbiSlots ce1Body.argumentCount ce1Spec ∧
    ValidTargetTypes ce1Body ce1Spec ∧
    AllReferencedLocalsInLiveMask ce1Spec.liveMask ce1Body ∧
    StorageMarkersOnlyOnDead ce1Spec.liveMask ce1Body.locals.length ce1Body ∧
    ¬ InjectiveOnLive ce1Spec ∧
    Behavior ce1SrcProg { args := [] } (.returned ⟨.bool false, ⟨[]⟩⟩) ∧
    ¬ Behavior ce1TgtProg { args := [] } (.returned ⟨.bool false, ⟨[]⟩⟩) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨by decide, fun i hi => ?_⟩
    cases i with | zero => exact ⟨rfl, rfl⟩ | succ k => cases hi
  · refine ⟨rfl, by decide, by decide, by decide, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨by decide, rfl⟩
    | succ i1 => cases i1 with
      | zero => exact ⟨by decide, rfl⟩
      | succ i2 => cases i2 with
        | zero => exact ⟨by decide, rfl⟩
        | succ _ => cases hi
  · intro hInj
    have hEq : (1 : LocalId) = 2 := hInj 1 2 rfl rfl rfl
    cases hEq
  · unfold Behavior ReachesResult
    have hInit : initState ce1SrcProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    rw [hInit]
    have hReach : Reaches ce1SrcProg
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none, .live none] }], callerMem := ⟨[]⟩ }
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 3, locals := [.live (some (.bool false)), .live (some (.bool false)), .live (some (.bool true))] }], callerMem := ⟨[]⟩ } :=
      Reaches.tail (Reaches.tail (Reaches.tail (Reaches.refl _) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩
    exact ⟨_, hReach, ⟨0, rfl, rfl⟩⟩
  · intro hBad
    have hInitTgt : initState ce1TgtProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    have hExecTgt : execOutcomeState ce1TgtProg (fun o => o = .returned ⟨.bool true, ⟨[]⟩⟩) (fun _ => False) 5
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    have hEq := behavior_unique_of_exec hInitTgt hExecTgt hBad
    cases hEq

/-- **CE2a (Compacting a still-referenced local breaks operational equivalence):**
Marking referenced local `_1` as dead in `liveMask` (mapping `_1 -> 1` outside
`targetLocals = [.bool]`) satisfies `PreservesAbiSlots`, `InjectiveOnLive`,
`ValidTargetTypes`, and `StorageMarkersOnlyOnDead`, while failing
`AllReferencedLocalsInLiveMask` and turning a valid return into `.fault .unsupported`. -/
noncomputable def ce2aBody : Body :=
  { argumentCount := 0
    locals := [.bool, .bool]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }] }

noncomputable def ce2aSpec : CompactionSpec :=
  { liveMask := [true, false]
    slotMap := [0, 1]
    targetLocals := [.bool] }

noncomputable def ce2aSrcProg : Program :=
  { bodies := [ce2aBody], pointerWidthBits := 64, mirProfileVersion := 1 }

noncomputable def ce2aTgtProg : Program :=
  compactProgram [ce2aSpec] ce2aSrcProg

theorem ce2a_referenced_local_compacted_breaks_eval :
    PreservesAbiSlots ce2aBody.argumentCount ce2aSpec ∧
    InjectiveOnLive ce2aSpec ∧
    ValidTargetTypes ce2aBody ce2aSpec ∧
    StorageMarkersOnlyOnDead ce2aSpec.liveMask ce2aBody.locals.length ce2aBody ∧
    ¬ AllReferencedLocalsInLiveMask ce2aSpec.liveMask ce2aBody ∧
    Behavior ce2aSrcProg { args := [] } (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
    (∀ out, ¬ Behavior ce2aTgtProg { args := [] } out) := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨by decide, fun i hi => ?_⟩
    cases i with | zero => exact ⟨rfl, rfl⟩ | succ k => cases hi
  · intro i j hi hj _
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j1 => cases j1 with | zero => cases hj | succ _ => cases hj
    | succ i1 => cases i1 with | zero => cases hi | succ _ => cases hi
  · refine ⟨rfl, by decide, by decide, by decide, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨by decide, rfl⟩
    | succ i1 => cases i1 with | zero => cases hi | succ _ => cases hi
  · intro hRef
    unfold AllReferencedLocalsInLiveMask at hRef
    cases hRef
  · unfold Behavior ReachesResult
    have hInit : initState ce2aSrcProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    rw [hInit]
    have hReach : Reaches ce2aSrcProg
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ }
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 2, locals := [.live (some (.bool true)), .live (some (.bool true))] }], callerMem := ⟨[]⟩ } :=
      Reaches.tail (Reaches.tail (Reaches.refl _) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩
    exact ⟨_, hReach, ⟨0, rfl, rfl⟩⟩
  · intro out hBad
    have hInitTgt : initState ce2aTgtProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none] }], callerMem := ⟨[]⟩ } := rfl
    have hExecFault : execOutcomeState ce2aTgtProg (fun _ => False) (fun _ => True) 3
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none] }], callerMem := ⟨[]⟩ } := by exact True.intro
    exact not_behavior_of_execFault hInitTgt hExecFault out hBad

/-- **CE2b (Moving parameter ABI slot `_1` breaks entry/return behavior):**
Permuting `_1 <-> _2` satisfies `InjectiveOnLive`, `ValidTargetTypes`,
`AllReferencedLocalsInLiveMask`, and `StorageMarkersOnlyOnDead`, while failing
`PreservesAbiSlots` and breaking well-formed entry on valid `.bool` input. -/
noncomputable def ce2bBody : Body :=
  { argumentCount := 1
    locals := [.bool, .bool, .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }] }

noncomputable def ce2bSpec : CompactionSpec :=
  { liveMask := [true, true, true]
    slotMap := [0, 2, 1]
    targetLocals := [.bool, .unit, .bool] }

noncomputable def ce2bSrcProg : Program :=
  { bodies := [ce2bBody], pointerWidthBits := 64, mirProfileVersion := 1 }

noncomputable def ce2bTgtProg : Program :=
  compactProgram [ce2bSpec] ce2bSrcProg

theorem ce2b_abi_arg_slot_not_preserved_breaks_eval :
    InjectiveOnLive ce2bSpec ∧
    ValidTargetTypes ce2bBody ce2bSpec ∧
    AllReferencedLocalsInLiveMask ce2bSpec.liveMask ce2bBody ∧
    StorageMarkersOnlyOnDead ce2bSpec.liveMask ce2bBody.locals.length ce2bBody ∧
    ¬ PreservesAbiSlots ce2bBody.argumentCount ce2bSpec ∧
    Behavior ce2bSrcProg { args := [.bool true] } (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
    (∀ out, ¬ Behavior ce2bTgtProg { args := [.bool true] } out) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro i j hi hj hMap
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j1 => cases j1 with | zero => cases hMap | succ j2 => cases j2 with | zero => cases hMap | succ _ => cases hj
    | succ i1 =>
      cases i1 with
      | zero =>
        cases j with | zero => cases hMap | succ j1 => cases j1 with | zero => rfl | succ j2 => cases j2 with | zero => cases hMap | succ _ => cases hj
      | succ i2 =>
        cases i2 with
        | zero =>
          cases j with | zero => cases hMap | succ j1 => cases j1 with | zero => cases hMap | succ j2 => cases j2 with | zero => rfl | succ _ => cases hj
        | succ _ => cases hi
  · refine ⟨rfl, by decide, by decide, by decide, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨by decide, rfl⟩
    | succ i1 => cases i1 with | zero => exact ⟨by decide, rfl⟩ | succ i2 => cases i2 with | zero => exact ⟨by decide, rfl⟩ | succ _ => cases hi
  · intro ⟨_, hMap⟩
    have h1 := (hMap 1 (Nat.le_refl 1)).2
    cases h1
  · unfold Behavior ReachesResult
    have hInit : initState ce2bSrcProg { args := [.bool true] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live (some (.bool true)), .live (some .unit)] }], callerMem := ⟨[]⟩ } := rfl
    rw [hInit]
    have hReach : Reaches ce2bSrcProg
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live (some (.bool true)), .live (some .unit)] }], callerMem := ⟨[]⟩ }
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := [.live (some (.bool true)), .live (some (.bool true)), .live (some .unit)] }], callerMem := ⟨[]⟩ } :=
      Reaches.tail (Reaches.refl _) ⟨0, rfl, rfl⟩
    exact ⟨_, hReach, ⟨0, rfl, rfl⟩⟩
  · intro out hBad
    unfold Behavior ReachesResult at hBad
    have hErr : initState ce2bTgtProg { args := [.bool true] } = .error .unsupported := rfl
    rw [hErr] at hBad
    cases hBad

/-- **CE2c (Moving return slot `_0` breaks `.return_` behavior):**
Swapping return slot `_0` into local `1` satisfies `InjectiveOnLive`,
`ValidTargetTypes`, `AllReferencedLocalsInLiveMask`, and `StorageMarkersOnlyOnDead`,
while failing `PreservesAbiSlots` and causing `.return_` to fault `.undefined` on
uninitialized `_0`. -/
noncomputable def ce2cBody : Body :=
  { argumentCount := 0
    locals := [.bool, .bool]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.use (.constant ⟨.bool, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .return_
    }] }

noncomputable def ce2cSpec : CompactionSpec :=
  { liveMask := [true, true]
    slotMap := [1, 0]
    targetLocals := [.bool, .bool] }

noncomputable def ce2cSrcProg : Program :=
  { bodies := [ce2cBody], pointerWidthBits := 64, mirProfileVersion := 1 }

noncomputable def ce2cTgtProg : Program :=
  compactProgram [ce2cSpec] ce2cSrcProg

theorem ce2c_return_slot_zero_moved_breaks_eval :
    InjectiveOnLive ce2cSpec ∧
    ValidTargetTypes ce2cBody ce2cSpec ∧
    AllReferencedLocalsInLiveMask ce2cSpec.liveMask ce2cBody ∧
    StorageMarkersOnlyOnDead ce2cSpec.liveMask ce2cBody.locals.length ce2cBody ∧
    ¬ PreservesAbiSlots ce2cBody.argumentCount ce2cSpec ∧
    Behavior ce2cSrcProg { args := [] } (.returned ⟨.bool true, ⟨[]⟩⟩) ∧
    ReachesResult ce2cTgtProg { args := [] } (.fault .undefined) ∧
    (∀ out, ¬ Behavior ce2cTgtProg { args := [] } out) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hMap
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j1 => cases j1 with | zero => cases hMap | succ _ => cases hj
    | succ i1 =>
      cases i1 with
      | zero => cases j with | zero => cases hMap | succ j1 => cases j1 with | zero => rfl | succ _ => cases hj
      | succ _ => cases hi
  · refine ⟨rfl, by decide, by decide, by decide, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨by decide, rfl⟩
    | succ i1 => cases i1 with | zero => exact ⟨by decide, rfl⟩ | succ _ => cases hi
  · intro ⟨_, hMap⟩
    have h0 := (hMap 0 (Nat.zero_le 0)).2
    cases h0
  · unfold Behavior ReachesResult
    have hInit : initState ce2cSrcProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    rw [hInit]
    have hReach : Reaches ce2cSrcProg
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ }
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := [.live (some (.bool true)), .live none] }], callerMem := ⟨[]⟩ } :=
      Reaches.tail (Reaches.refl _) ⟨0, rfl, rfl⟩
    exact ⟨_, hReach, ⟨0, rfl, rfl⟩⟩
  · unfold ReachesResult
    have hInitTgt : initState ce2cTgtProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    rw [hInitTgt]
    have hReachTgt : Reaches ce2cTgtProg
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ }
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := [.live none, .live (some (.bool true))] }], callerMem := ⟨[]⟩ } :=
      Reaches.tail (Reaches.refl _) ⟨0, rfl, rfl⟩
    exact ⟨_, hReachTgt, ⟨0, rfl, rfl⟩⟩
  · intro out hBad
    have hInitTgt : initState ce2cTgtProg { args := [] } =
        .ok { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := rfl
    have hExecFault : execOutcomeState ce2cTgtProg (fun _ => False) (fun _ => True) 3
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.live none, .live none] }], callerMem := ⟨[]⟩ } := by exact True.intro
    exact not_behavior_of_execFault hInitTgt hExecFault out hBad

end AnnealMirR3Compaction
