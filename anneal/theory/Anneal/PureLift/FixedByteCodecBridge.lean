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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.InitLemmas
public import Anneal.LeBytes
public import Anneal.ListChunks
public import Anneal.Core.BitValidity
public import Anneal.Core.FixedByteCodec
public import Anneal.MirTotal.Ops
public import Anneal.ByteSubLens.Lens
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin

public section

namespace Anneal.PureLift

open Anneal.InitLemmas Anneal.LeBytes Anneal.ListChunks Anneal.Core
open Anneal.MirTotal Anneal.ByteSubLens
open Trusted.MirAst Trusted.MirSemantics

/-!
# `FixedByteCodec` ↔ `ByteSubLens` & `SpatialPin` Bridge

Connects `Anneal.Core.FixedByteCodec` to both:

1. **Part A — Typed `ByteSubLens` `MemoryState` Lenses (`TypedByteSubLens`):**
   Pairs a `ByteSubLens` (`allocId`, `offset`, `size = n`) over
   `Trusted.MirSemantics.MemoryState` with `c : FixedByteCodec α n`
   (`typedSubLensGet` / `typedSubLensPut`, inheriting `ByteSubLens`'s `.mut`
   allocation requirement for both reads and writes), bridges to
   `Trusted.MirSemantics` (`findAllocation`, `readBytes`, `writeBytes`), proves
   `typedSubLens_get_put` (write-then-read), `typedSubLens_put_get` (read-then-
   write under canonical / provenance-free conditions, plus `LawfulLens`
   assembly), `typedSubLens_put_put`, `typedSubLens_get_put_disjoint`, adjacent
   struct-field `prod` split-borrow decomposition, `CodecTransmuteSound` view
   casts, and fail-closed `.uninit` padding rejection.
2. **Part B — `FixedByteCodec` ↔ `PureLift.SpatialPin` Bridge:**
   Lifts any provenance-free `FixedByteCodec α n` (`c.NoProvCodec`) to a
   `SpatialCodec Val` (`spatialCodecOfFixedByteCodec`) mapping
   `AllocByte.init b none ↔ CellVal.rawByte b` and
   `AllocByte.uninit ↔ CellVal.uninit` on exact `n`-cell windows (tagging
   non-`α` fallback `Val`s at width `n + 1` so length-preserving spatial
   mutations can never smuggle `.init` payloads into an `n`-byte view), proves
   `LawfulCodec`, connects `IsInitCodec` (`IntoBytes`) to `hasUninitCell`, and
   proves clean `freezeToSpatialInState` → `reabsorbFromSpatialInState`
   round-trips as well as fail-closed rejection when any cell is `.uninit` or
   fails `c.decode`.
-/

/-! ## 0. Private Constructive `Bool`, `Nat`, `List`, and Alignment Helpers -/

private theorem br_false_ne_true (h : false = true) : False := by
  nomatch h

private theorem br_if_true {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

private theorem br_if_false {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem br_if_bool_true {α : Type} {c : Bool} {a b : α}
    (hc : c = true) : (if c then a else b) = a := by
  subst hc
  rfl

private theorem br_if_bool_false {α : Type} {c : Bool} {a b : α}
    (hc : c = false) : (if c then a else b) = b := by
  subst hc
  rfl

private theorem br_ite_false_true {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

private theorem br_band_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (br_false_ne_true h)
  | true => rfl

private theorem br_band_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (br_false_ne_true h)
  | true => exact h

private theorem br_bor_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => exact False.elim (Bool.noConfusion h)
  | false => exact ⟨rfl, h⟩

private theorem br_nat_beq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem br_nat_eq_of_beq {a b : Nat} (h : Nat.beq a b = true) :
    a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (br_false_ne_true h)
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (br_false_ne_true h)
    | succ b' => exact congrArg Nat.succ (ih h)

private theorem br_nat_beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨br_nat_eq_of_beq, fun h => by subst h; exact br_nat_beq_refl a⟩

private theorem br_nat_blt_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  constructor
  · intro h
    exact Nat.le_of_ble_eq_true h
  · intro h
    exact Eq.mpr Nat.ble_eq h

private theorem br_nat_ble_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b :=
  ⟨Eq.mp Nat.ble_eq, Eq.mpr Nat.ble_eq⟩

private theorem br_nat_beq_zero_false_of_lt {n : Nat} (hPos : 0 < n) :
    Nat.beq n 0 = false := by
  cases n with
  | zero => nomatch hPos
  | succ _ => rfl

private theorem br_nat_pow_pos (b n : Nat) (hb : 0 < b) : 0 < Nat.pow b n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ _ ih => exact Nat.mul_pos ih hb

private theorem br_nat_pow_add (b m n : Nat) :
    Nat.pow b (m + n) = Nat.pow b m * Nat.pow b n := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    exact (Nat.mul_one (Nat.pow b m)).symm
  | succ n ih =>
    rw [Nat.add_succ]
    change Nat.pow b (m + n) * b = Nat.pow b m * (Nat.pow b n * b)
    rw [ih, Nat.mul_assoc]

private theorem br_nat_add_sub_of_le {a b : Nat} (h : a ≤ b) :
    a + (b - a) = b := by
  revert b
  induction a with
  | zero => intro b _; rw [Nat.zero_add, Nat.sub_zero]
  | succ a' ih =>
    intro b h
    cases b with
    | zero => nomatch h
    | succ b' =>
      rw [Nat.succ_sub_succ, Nat.succ_add]
      exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

private theorem br_nat_mod_mul_right (x y : Nat) :
    Nat.mod (x * y) x = 0 := by
  have h0 : HMod.hMod (0 + x * y) x = HMod.hMod 0 x :=
    Nat.add_mul_mod_self_left 0 x y
  rw [Nat.zero_add, Nat.zero_mod] at h0
  exact h0

private theorem br_nat_mod_dvd_of_le {off alSmall alBig : Nat}
    (hLe : alSmall ≤ alBig) (hMod : Nat.mod off (Nat.pow 2 alBig) = 0) :
    Nat.mod off (Nat.pow 2 alSmall) = 0 := by
  have hd : alBig = alSmall + (alBig - alSmall) :=
    (br_nat_add_sub_of_le hLe).symm
  rw [hd, br_nat_pow_add] at hMod
  have hSplit :
      Nat.pow 2 alSmall * Nat.pow 2 (alBig - alSmall) *
          HDiv.hDiv off (Nat.pow 2 alSmall * Nat.pow 2 (alBig - alSmall)) +
        Nat.mod off (Nat.pow 2 alSmall * Nat.pow 2 (alBig - alSmall)) = off :=
    Nat.div_add_mod off (Nat.pow 2 alSmall * Nat.pow 2 (alBig - alSmall))
  rw [hMod, Nat.add_zero, Nat.mul_assoc] at hSplit
  rw [← hSplit]
  exact br_nat_mod_mul_right (Nat.pow 2 alSmall) _

private theorem br_nat_mod_add_zero {x y m : Nat}
    (hx : Nat.mod x m = 0) (hy : Nat.mod y m = 0) :
    Nat.mod (x + y) m = 0 := by
  have hdx : m * HDiv.hDiv x m + Nat.mod x m = x := Nat.div_add_mod x m
  have hdy : m * HDiv.hDiv y m + Nat.mod y m = y := Nat.div_add_mod y m
  rw [hx, Nat.add_zero] at hdx
  rw [hy, Nat.add_zero] at hdy
  rw [← hdx, ← hdy, ← Nat.mul_add]
  exact br_nat_mod_mul_right m (HDiv.hDiv x m + HDiv.hDiv y m)

private theorem br_length_drop {α : Type} (n : Nat) (xs : List α) :
    (xs.drop n).length = xs.length - n := by
  induction n generalizing xs with
  | zero => rw [List.drop_zero, Nat.sub_zero]
  | succ n ih =>
    cases xs with
    | nil => rw [List.drop_nil, List.length_nil, Nat.zero_sub]
    | cons _ rest => rw [List.drop_succ_cons, List.length_cons, ih, Nat.succ_sub_succ]

private theorem br_length_take_of_le {α : Type} {n : Nat} {xs : List α}
    (h : n ≤ xs.length) : (xs.take n).length = n := by
  revert xs
  induction n with
  | zero => intro _ _; rfl
  | succ n' ih =>
    intro xs h
    cases xs with
    | nil => nomatch h
    | cons _ rest =>
      rw [List.take_succ_cons, List.length_cons]
      exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

private theorem br_take_take_of_le {α : Type} :
    ∀ {m n : Nat} (xs : List α), m ≤ n → (xs.take n).take m = xs.take m
  | 0, _, _, _ => by rw [List.take_zero, List.take_zero]
  | _ + 1, 0, _, h => by nomatch h
  | m + 1, n + 1, [], _ => rfl
  | m + 1, n + 1, x :: xs, h => by
    rw [List.take_succ_cons, List.take_succ_cons, List.take_succ_cons]
    exact congrArg (List.cons x) (br_take_take_of_le xs (Nat.le_of_succ_le_succ h))

private theorem br_drop_take_add {α : Type} :
    ∀ (m n : Nat) (xs : List α), (xs.take (m + n)).drop m = (xs.drop m).take n
  | 0, n, xs => by rw [Nat.zero_add, List.drop_zero, List.drop_zero]
  | m + 1, n, [] => by
    rw [List.take_nil, List.drop_nil, List.take_nil]
  | m + 1, n, _ :: xs => by
    rw [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons]
    exact br_drop_take_add m n xs

private theorem br_drop_drop {α : Type} :
    ∀ (m n : Nat) (xs : List α), (xs.drop m).drop n = xs.drop (m + n)
  | 0, n, xs => by rw [List.drop_zero, Nat.zero_add]
  | m + 1, n, [] => by rw [List.drop_nil, List.drop_nil, List.drop_nil]
  | m + 1, n, _ :: xs => by
    rw [List.drop_succ_cons, Nat.succ_add, List.drop_succ_cons]
    exact br_drop_drop m n xs

private theorem br_splice_length {α : Type} (off : Nat) (mid xs : List α)
    (h : off + mid.length ≤ xs.length) :
    (xs.take off ++ mid ++ xs.drop (off + mid.length)).length = xs.length := by
  have hOffLe : off ≤ xs.length := Nat.le_trans (Nat.le_add_right off mid.length) h
  rw [List.length_append, List.length_append, br_length_take_of_le hOffLe,
      br_length_drop, br_nat_add_sub_of_le h]

private theorem br_splice_adjacent_eq {α : Type} (off : Nat)
    (bs1 bs2 xs : List α) (h : off + (bs1.length + bs2.length) ≤ xs.length) :
    let mid1 := xs.take off ++ bs1 ++ xs.drop (off + bs1.length)
    mid1.take (off + bs1.length) ++ bs2 ++
        mid1.drop (off + bs1.length + bs2.length) =
      xs.take off ++ (bs1 ++ bs2) ++ xs.drop (off + (bs1.length + bs2.length)) := by
  intro mid1
  have hOffLe : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off (bs1.length + bs2.length)) h
  have hPreLen : (xs.take off ++ bs1).length = off + bs1.length := by
    rw [List.length_append, br_length_take_of_le hOffLe]
  have hTakeMid1 : mid1.take (off + bs1.length) = xs.take off ++ bs1 := by
    dsimp only [mid1]
    have hT :=
      list_take_append_left (xs.take off ++ bs1) (xs.drop (off + bs1.length))
    rw [hPreLen] at hT
    exact hT
  have hDropMid1 :
      mid1.drop (off + bs1.length + bs2.length) =
        xs.drop (off + (bs1.length + bs2.length)) := by
    dsimp only [mid1]
    have hD :=
      list_drop_append_left (xs.take off ++ bs1) (xs.drop (off + bs1.length))
    rw [hPreLen] at hD
    rw [← br_drop_drop (off + bs1.length) bs2.length, hD, br_drop_drop,
        Nat.add_assoc]
  rw [hTakeMid1, hDropMid1, List.append_assoc (xs.take off) bs1 bs2]

private theorem isAlignedComp_of_le (a : Allocation) (off alSmall alBig : Nat)
    (hLe : alSmall ≤ alBig) (hAl : isAlignedComp a off alBig = true) :
    isAlignedComp a off alSmall = true := by
  dsimp only [isAlignedComp] at hAl
  have hBleBig := br_band_left hAl
  have hModBig := br_nat_eq_of_beq (br_band_right hAl)
  have hLeBig : alBig ≤ a.alignLog2 := (br_nat_ble_iff _ _).mp hBleBig
  have hBleSmall : Nat.ble alSmall a.alignLog2 = true :=
    (br_nat_ble_iff _ _).mpr (Nat.le_trans hLe hLeBig)
  have hModSmall : Nat.mod off (Nat.pow 2 alSmall) = 0 :=
    br_nat_mod_dvd_of_le hLe hModBig
  dsimp only [isAlignedComp]
  rw [hBleSmall, (br_nat_beq_iff _ _).mpr hModSmall]
  rfl

private theorem isAlignedComp_add (a : Allocation) (off n1 alBig al2 : Nat)
    (hLe : al2 ≤ alBig)
    (hModN1 : Nat.mod n1 (Nat.pow 2 al2) = 0)
    (hAl : isAlignedComp a off alBig = true) :
    isAlignedComp a (off + n1) al2 = true := by
  have hAl2 : isAlignedComp a off al2 = true :=
    isAlignedComp_of_le a off al2 alBig hLe hAl
  dsimp only [isAlignedComp] at hAl2
  have hBle2 := br_band_left hAl2
  have hModOff := br_nat_eq_of_beq (br_band_right hAl2)
  have hModSum := br_nat_mod_add_zero hModOff hModN1
  dsimp only [isAlignedComp]
  rw [hBle2, (br_nat_beq_iff _ _).mpr hModSum]
  rfl

private theorem list_drop_take_adjacent_fst {α : Type} (off n1 n2 : Nat)
    (xs : List α) :
    ((xs.drop off).take (n1 + n2)).take n1 = (xs.drop off).take n1 :=
  br_take_take_of_le (xs.drop off) (Nat.le_add_right n1 n2)

private theorem list_drop_take_adjacent_snd {α : Type} (off n1 n2 : Nat)
    (xs : List α) :
    ((xs.drop off).take (n1 + n2)).drop n1 = (xs.drop (off + n1)).take n2 := by
  rw [br_drop_take_add n1 n2 (xs.drop off), br_drop_drop]

private theorem br_mutability_eq_shared (m : Mutability)
    (h : mutabilityIsMut m = false) : m = .shared :=
  @Mutability.casesOn (fun x => mutabilityIsMut x = false → x = .shared) m
    (fun _ => rfl) (fun hf => nomatch hf) h

private theorem br_mutability_eq_mut (m : Mutability)
    (h : mutabilityIsMut m = true) : m = .mut :=
  @Mutability.casesOn (fun x => mutabilityIsMut x = true → x = .mut) m
    (fun hf => nomatch hf) (fun _ => rfl) h

private theorem br_nat_add_pos_left {m : Nat} (h : 0 < m) (n : Nat) :
    0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right m n)

private theorem br_nat_bne_self (n : Nat) : (n != n) = false := by
  change (!(n == n)) = false
  rw [beq_self_eq_true n]
  rfl

private theorem br_and_not_true (x : Bool) : (x && !true) = false := by
  cases x <;> rfl

private theorem br_false_and (x : Bool) : (false && x) = false := rfl

private theorem br_foldr_cons {α β : Type} (f : α → β → β) (z : β) (a : α)
    (l : List α) : (a :: l).foldr f z = f a (l.foldr f z) := rfl

private theorem br_dite_pos {c : Prop} [Decidable c] {α : Type}
    {t : c → α} {e : ¬ c → α} (hc : c) :
    (if h : c then t h else e h) = t hc := by
  cases ‹Decidable c› with
  | isFalse h => exact False.elim (h hc)
  | isTrue _ => rfl

private theorem br_dite_neg {c : Prop} [Decidable c] {α : Type}
    {t : c → α} {e : ¬ c → α} (hnc : ¬ c) :
    (if h : c then t h else e h) = e hnc := by
  cases ‹Decidable c› with
  | isFalse _ => rfl
  | isTrue h => exact False.elim (hnc h)

private theorem br_length_reverseAux {α : Type} (xs acc : List α) :
    (List.reverseAux xs acc).length = xs.length + acc.length := by
  induction xs generalizing acc with
  | nil => rw [List.reverseAux_nil, List.length_nil, Nat.zero_add]
  | cons a rest ih =>
    rw [List.reverseAux_cons, ih, List.length_cons, List.length_cons,
        Nat.succ_add, Nat.add_succ]

private theorem br_length_reverse {α : Type} (xs : List α) :
    xs.reverse.length = xs.length := by
  unfold List.reverse
  rw [br_length_reverseAux, List.length_nil, Nat.add_zero]

private theorem br_reverse_append {α : Type} (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  induction xs with
  | nil => rw [List.nil_append, List.reverse_nil, List.append_nil]
  | cons a rest ih =>
    rw [List.cons_append, List.reverse_cons, List.reverse_cons, ih,
        List.append_assoc]

private theorem br_reverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, br_reverse_append, ih]
    rfl

private theorem br_toLeBytes_fromLeBytes (bs : List (BitVec 8)) (sz : Nat)
    (hLen : bs.length = sz) :
    toLeBytes sz (BitVec.ofNat (sz * 8) (fromLeBytes bs)) = bs := by
  apply fromLeBytes_injective
  · rw [toLeBytes_length, hLen]
  · rw [fromLeBytes_toLeBytes]
    subst hLen
    exact fromLeBytesBv_toNat bs

/-! ## 1. Part A: Typed `ByteSubLens` `MemoryState` Lenses -/

/-- Decode the byte window focused by `ByteSubLens` `l` in `MemoryState` `mem`
via `FixedByteCodec α n` (requires a `.mut` allocation, inherited from
`ByteSubLens`; `.shared` allocations are outside this `&mut` lens and return
`none`). -/
@[expose] def typedSubLensGet {α : Type} {n : Nat} (l : ByteSubLens)
    (c : FixedByteCodec α n) (mem : MemoryState) : Option α :=
  (byteSubLensGet l mem).bind c.decode

/-- Encode `v : α` via `FixedByteCodec α n` and write it into the byte window
focused by `ByteSubLens` `l` in `MemoryState` `mem`. -/
@[expose] def typedSubLensPut {α : Type} {n : Nat} (l : ByteSubLens)
    (c : FixedByteCodec α n) (mem : MemoryState) (v : α) :
    Option MemoryState :=
  byteSubLensPut l mem (c.encode v)

/-- Agreement between computable `typedSubLensGet` and
`Trusted.MirSemantics.{findAllocation, readBytes}`. -/
theorem typedSubLensGet_eq_mir {α : Type} {n : Nat} (l : ByteSubLens)
    (c : FixedByteCodec α n) (mem : MemoryState) :
    typedSubLensGet l c mem =
      (match Nat.blt 0 l.size with
       | false => none
       | true =>
         match findAllocation l.allocId mem.allocations with
         | none => none
         | some a =>
           match mutabilityIsMut a.mutability with
           | false => none
           | true =>
             match readBytes mem ⟨l.allocId, l.offset⟩ l.size l.alignLog2 with
             | .ok bs => some bs
             | .error _ => none).bind c.decode := by
  unfold typedSubLensGet
  rw [byteSubLensGet_eq_mir]
  rfl

/-- Agreement between computable `typedSubLensPut` and
`Trusted.MirSemantics.writeBytes`. -/
theorem typedSubLensPut_eq_mir {α : Type} {n : Nat} (l : ByteSubLens)
    (c : FixedByteCodec α n) (mem : MemoryState) (v : α) :
    typedSubLensPut l c mem v =
      match Nat.blt 0 l.size && Nat.beq (c.encode v).length l.size with
      | false => none
      | true =>
        match writeBytes mem ⟨l.allocId, l.offset⟩ l.alignLog2 (c.encode v) with
        | .ok m' => some m'
        | .error _ => none := by
  unfold typedSubLensPut
  exact byteSubLensPut_eq_mir l mem (c.encode v)

/-- Packaged partial lens view combining a positive-width `ByteSubLens`
(`lens.size = n`) and `c : FixedByteCodec α n`. -/
structure TypedByteSubLens (α : Type) (n : Nat) where
  lens : ByteSubLens
  codec : FixedByteCodec α n
  pos : 0 < n
  size_eq : lens.size = n

namespace TypedByteSubLens

@[expose] def get {α : Type} {n : Nat} (tbl : TypedByteSubLens α n)
    (mem : MemoryState) : Option α :=
  typedSubLensGet tbl.lens tbl.codec mem

@[expose] def put {α : Type} {n : Nat} (tbl : TypedByteSubLens α n)
    (mem : MemoryState) (v : α) : Option MemoryState :=
  typedSubLensPut tbl.lens tbl.codec mem v

@[expose] def toLens {α : Type} {n : Nat} (tbl : TypedByteSubLens α n) :
    Lens MemoryState α where
  get := tbl.get
  put := tbl.put

end TypedByteSubLens

/-! ### 1a. Canonical, Provenance-Free Canonical, and Init-Decoded Codecs -/

/-- Full canonicality (`c.decode bs = some v → c.encode v = bs` on all byte
lists, e.g., zero-byte ZST or provenance-rejecting canonical encodings). -/
@[expose] def CanonicalCodec {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ (bs : List AllocByte) (v : α), c.decode bs = some v → c.encode v = bs

/-- Provenance-free canonicality (`c.decode bs = some v → c.encode v = bs`
whenever `NoProvBytes bs` holds), satisfied by standard unpadded primitive,
product, and array codecs over `AllocByte`. -/
@[expose] def NoProvCanonicalCodec {α : Type} {n : Nat} (c : FixedByteCodec α n) :
    Prop :=
  ∀ (bs : List AllocByte) (v : α),
    NoProvBytes bs → c.decode bs = some v → c.encode v = bs

/-- Every byte list accepted by `c.decode` is fully initialized
(`AllBytesInit bs`), ruling out `.uninit` padding acceptance. -/
@[expose] def InitDecodedCodec {α : Type} {n : Nat} (c : FixedByteCodec α n) : Prop :=
  ∀ (bs : List AllocByte) (v : α), c.decode bs = some v → AllBytesInit bs

theorem canonical_implies_noProvCanonical {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hCan : CanonicalCodec c) :
    NoProvCanonicalCodec c :=
  fun bs v _ hDec => hCan bs v hDec

theorem canonical_zst : CanonicalCodec FixedByteCodec.zst := by
  intro bs v hDec
  cases v
  cases bs with
  | nil => rfl
  | cons _ _ => nomatch hDec

theorem initDecoded_zst : InitDecodedCodec FixedByteCodec.zst := by
  intro bs _ hDec
  cases bs with
  | nil => rfl
  | cons _ _ => nomatch hDec

private theorem noProvBytes_cons_head_none {b : UInt8}
    {prov : Option AllocId} {rest : List AllocByte}
    (hNoProv : NoProvBytes (AllocByte.init b prov :: rest)) :
    prov = none ∧ NoProvBytes rest := by
  cases prov with
  | none => exact ⟨rfl, hNoProv⟩
  | some _ =>
    dsimp [NoProvBytes] at hNoProv
    nomatch hNoProv

private theorem noProvBytes_take {n : Nat} {bs : List AllocByte}
    (hNoProv : NoProvBytes bs) : NoProvBytes (bs.take n) := by
  revert bs
  induction n with
  | zero => intro _ _; rfl
  | succ n' ih =>
    intro bs hNoProv
    cases bs with
    | nil => rfl
    | cons hd tl =>
      cases hd with
      | uninit =>
        rw [List.take_succ_cons]
        exact ih hNoProv
      | init b prov =>
        have hSplit := noProvBytes_cons_head_none hNoProv
        rw [hSplit.1, List.take_succ_cons]
        exact ih hSplit.2

private theorem noProvBytes_drop {n : Nat} {bs : List AllocByte}
    (hNoProv : NoProvBytes bs) : NoProvBytes (bs.drop n) := by
  revert bs
  induction n with
  | zero => intro _ hNoProv; exact hNoProv
  | succ n' ih =>
    intro bs hNoProv
    cases bs with
    | nil => rfl
    | cons hd tl =>
      cases hd with
      | uninit =>
        rw [List.drop_succ_cons]
        exact ih hNoProv
      | init b prov =>
        have hSplit := noProvBytes_cons_head_none hNoProv
        rw [List.drop_succ_cons]
        exact ih hSplit.2

private theorem rawBytes?_eq_some_of_noProv {bs : List AllocByte}
    {raw : List UInt8} (hNoProv : NoProvBytes bs)
    (hRaw : rawBytes? bs = some raw) :
    raw.map (fun b => AllocByte.init b none) = bs := by
  revert raw
  induction bs with
  | nil =>
    intro raw hRaw
    injection hRaw with hNil
    subst hNil
    rfl
  | cons hd tl ih =>
    intro raw hRaw
    cases hd with
    | uninit => nomatch hRaw
    | init b prov =>
      have hSplit := noProvBytes_cons_head_none hNoProv
      dsimp only [rawBytes?] at hRaw
      cases hTail : rawBytes? tl with
      | none =>
        change (match rawBytes? tl with
          | some t => some (b :: t)
          | none => none) = some raw at hRaw
        rw [hTail] at hRaw
        nomatch hRaw
      | some t =>
        change (match rawBytes? tl with
          | some t => some (b :: t)
          | none => none) = some raw at hRaw
        rw [hTail] at hRaw
        injection hRaw with hRawEq
        subst hRawEq
        rw [List.map_cons, ih hSplit.2 hTail, hSplit.1]

private theorem rawBytes?_allBytesInit {bs : List AllocByte}
    {raw : List UInt8} (hRaw : rawBytes? bs = some raw) : AllBytesInit bs := by
  rw [rawBytes?_eq_initBytes?] at hRaw
  exact (allBytesInit_of_initBytes?_eq_some hRaw).1

private theorem list_take_append_drop_len {α : Type} (n : Nat) (xs : List α) :
    xs.take n ++ xs.drop n = xs := by
  revert xs
  induction n with
  | zero => intro _; rfl
  | succ n' ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons hd tl =>
      rw [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      exact congrArg (List.cons hd) (ih tl)

theorem noProvCanonical_boolCodec : NoProvCanonicalCodec boolCodec := by
  intro bs v hNoProv hDec
  unfold boolCodec FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases bs with
  | nil => nomatch hDec
  | cons b0 rest =>
    cases b0 with
    | uninit => nomatch hDec
    | init b prov =>
      cases rest with
      | cons _ _ => nomatch hDec
      | nil =>
        have hP := (noProvBytes_cons_head_none hNoProv).1
        subst hP
        dsimp only at hDec
        cases h0 : Nat.beq b.toNat 0 with
        | true =>
          rw [br_if_bool_true h0] at hDec
          injection hDec with hV
          subst hV
          have hb0 : b = 0 := by
            have hNat := br_nat_eq_of_beq h0
            cases b with
            | ofBitVec bv =>
              cases bv with
              | ofFin f =>
                cases f with
                | mk val isLt =>
                  change val = 0 at hNat
                  subst hNat
                  rfl
          subst hb0
          rfl
        | false =>
          rw [br_if_bool_false h0] at hDec
          cases h1 : Nat.beq b.toNat 1 with
          | true =>
            rw [br_if_bool_true h1] at hDec
            injection hDec with hV
            subst hV
            have hb1 : b = 1 := by
              have hNat := br_nat_eq_of_beq h1
              cases b with
              | ofBitVec bv =>
                cases bv with
                | ofFin f =>
                  cases f with
                  | mk val isLt =>
                    change val = 1 at hNat
                    subst hNat
                    rfl
            subst hb1
            rfl
          | false =>
            rw [br_if_bool_false h1] at hDec
            nomatch hDec

theorem initDecoded_boolCodec : InitDecodedCodec boolCodec := by
  intro bs v hDec
  unfold boolCodec FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases bs with
  | nil => nomatch hDec
  | cons b0 rest =>
    cases b0 with
    | uninit => nomatch hDec
    | init _ _ =>
      cases rest with
      | cons _ _ => nomatch hDec
      | nil => rfl

private theorem ui8_ofBitVec_toBitVec (b : UInt8) :
    UInt8.ofBitVec b.toBitVec = b := rfl

private theorem list_map_ui8_ofBitVec_toBitVec (raw : List UInt8) :
    (raw.map UInt8.toBitVec).map UInt8.ofBitVec = raw := by
  induction raw with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.map_cons, ui8_ofBitVec_toBitVec, ih]

private theorem list_map_alloc_of_ui8 {f : BitVec 8 → UInt8}
    (xs : List (BitVec 8)) :
    (xs.map f).map (fun b => AllocByte.init b none) =
      xs.map (fun b => AllocByte.init (f b) none) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]

private theorem uintBvCodec_encode_decode_bits (endian : TargetEndian)
    (sz : Nat) (hPos : 0 < sz) (raw : List UInt8) (hLen : raw.length = sz) :
    (uintBvCodec endian sz hPos).encode
      (BitVec.ofNat (sz * 8)
        (match endian with
         | .little => fromLeBytes (raw.map UInt8.toBitVec)
         | .big => fromBeBytes (raw.map UInt8.toBitVec))) =
      raw.map (fun b => AllocByte.init b none) := by
  have hBvsLen : (raw.map UInt8.toBitVec).length = sz := by
    rw [length_map_eq]
    exact hLen
  cases endian with
  | little =>
    rw [uintBvCodec_encode_little]
    have hVal :=
      br_toLeBytes_fromLeBytes (raw.map UInt8.toBitVec) sz hBvsLen
    change
      (toLeBytes sz (BitVec.ofNat (sz * 8)
        (fromLeBytes (raw.map UInt8.toBitVec)))).map
          (fun b => AllocByte.init (UInt8.ofBitVec b) none) =
        raw.map (fun b => AllocByte.init b none)
    rw [hVal, ← list_map_alloc_of_ui8, list_map_ui8_ofBitVec_toBitVec]
  | big =>
    rw [uintBvCodec_encode_big]
    have hBvsRevLen : (raw.map UInt8.toBitVec).reverse.length = sz := by
      rw [br_length_reverse]
      exact hBvsLen
    have hVal :
        toBeBytes sz (BitVec.ofNat (sz * 8)
            (fromBeBytes (raw.map UInt8.toBitVec))) =
          raw.map UInt8.toBitVec := by
      unfold toBeBytes fromBeBytes
      rw [br_toLeBytes_fromLeBytes (raw.map UInt8.toBitVec).reverse sz hBvsRevLen,
          br_reverse_reverse]
    change
      (toBeBytes sz (BitVec.ofNat (sz * 8)
        (fromBeBytes (raw.map UInt8.toBitVec)))).map
          (fun b => AllocByte.init (UInt8.ofBitVec b) none) =
        raw.map (fun b => AllocByte.init b none)
    rw [hVal, ← list_map_alloc_of_ui8, list_map_ui8_ofBitVec_toBitVec]

theorem noProvCanonical_uintBvCodec (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : NoProvCanonicalCodec (uintBvCodec endian sz hPos) := by
  intro bs v hNoProv hDec
  unfold uintBvCodec FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hBeq : Nat.beq bs.length sz with
  | false =>
    rw [br_if_bool_false hBeq] at hDec
    nomatch hDec
  | true =>
    rw [br_if_bool_true hBeq] at hDec
    have hLen : bs.length = sz := br_nat_eq_of_beq hBeq
    cases hRaw : rawBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw =>
      rw [hRaw] at hDec
      dsimp only at hDec
      injection hDec with hV
      subst hV
      have hRawLen : raw.length = sz := by
        have hEq := rawBytes?_eq_some_of_noProv hNoProv hRaw
        rw [← hEq, length_map_eq] at hLen
        exact hLen
      cases endian with
      | little =>
        rw [uintBvCodec_encode_decode_bits .little sz hPos raw hRawLen]
        exact rawBytes?_eq_some_of_noProv hNoProv hRaw
      | big =>
        rw [uintBvCodec_encode_decode_bits .big sz hPos raw hRawLen]
        exact rawBytes?_eq_some_of_noProv hNoProv hRaw

theorem initDecoded_uintBvCodec (endian : TargetEndian) (sz : Nat)
    (hPos : 0 < sz) : InitDecodedCodec (uintBvCodec endian sz hPos) := by
  intro bs _ hDec
  unfold uintBvCodec FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hBeq : Nat.beq bs.length sz with
  | false =>
    rw [br_if_bool_false hBeq] at hDec
    nomatch hDec
  | true =>
    rw [br_if_bool_true hBeq] at hDec
    cases hRaw : rawBytes? bs with
    | none =>
      rw [hRaw] at hDec
      nomatch hDec
    | some raw => exact rawBytes?_allBytesInit hRaw

theorem noProvCanonical_intBvCodec (endian : TargetEndian) (w : IntWidth) :
    NoProvCanonicalCodec (intBvCodec endian w) :=
  noProvCanonical_uintBvCodec endian (fbcByteSize w) (fbcByteSize_pos w)

theorem initDecoded_intBvCodec (endian : TargetEndian) (w : IntWidth) :
    InitDecodedCodec (intBvCodec endian w) :=
  initDecoded_uintBvCodec endian (fbcByteSize w) (fbcByteSize_pos w)

theorem noProvCanonical_prod {α β : Type} {m n : Nat}
    {c₁ : FixedByteCodec α m} {c₂ : FixedByteCodec β n}
    (h₁ : NoProvCanonicalCodec c₁) (h₂ : NoProvCanonicalCodec c₂) :
    NoProvCanonicalCodec (FixedByteCodec.prod c₁ c₂) := by
  intro bs p hNoProv hDec
  cases p with
  | mk a b =>
    have hProj := FixedByteCodec.prod_decode_projections c₁ c₂ hDec
    have hEnc1 := h₁ (bs.take m) a (noProvBytes_take hNoProv) hProj.2.1
    have hEnc2 := h₂ (bs.drop m) b (noProvBytes_drop hNoProv) hProj.2.2
    rw [FixedByteCodec.prod_encode_eq, hEnc1, hEnc2, list_take_append_drop_len]

theorem initDecoded_prod {α β : Type} {m n : Nat}
    {c₁ : FixedByteCodec α m} {c₂ : FixedByteCodec β n}
    (h₁ : InitDecodedCodec c₁) (h₂ : InitDecodedCodec c₂) :
    InitDecodedCodec (FixedByteCodec.prod c₁ c₂) := by
  intro bs p hDec
  cases p with
  | mk a b =>
    have hProj := FixedByteCodec.prod_decode_projections c₁ c₂ hDec
    have hi1 := h₁ (bs.take m) a hProj.2.1
    have hi2 := h₂ (bs.drop m) b hProj.2.2
    rw [← list_take_append_drop_len m bs]
    exact AllBytesInit_append hi1 hi2

private theorem noProvCanonical_decodeChunks {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hCan : NoProvCanonicalCodec c) :
    ∀ {k : Nat} {bs : List AllocByte}
      {xs : Subtype (fun xs : List α => xs.length = k)},
      NoProvBytes bs →
      FixedByteCodec.decodeChunks c k bs = some xs →
      FixedByteCodec.encodeElems c xs.val = bs
  | 0, [], ⟨[], _⟩, _, _ => rfl
  | 0, _ :: _, _, _, hDec => by nomatch hDec
  | k + 1, bs, ⟨xs, hxs⟩, hNoProv, hDec => by
    rw [FixedByteCodec.decodeChunks_succ] at hDec
    cases hBle : Nat.ble n bs.length with
    | false =>
      rw [br_if_bool_false hBle] at hDec
      nomatch hDec
    | true =>
      rw [br_if_bool_true hBle] at hDec
      cases hHead : c.decode (bs.take n) with
      | none =>
        rw [hHead] at hDec
        nomatch hDec
      | some hd =>
        rw [hHead] at hDec
        cases hTail : FixedByteCodec.decodeChunks c k (bs.drop n) with
        | none =>
          rw [hTail] at hDec
          nomatch hDec
        | some tlSub =>
          rw [hTail] at hDec
          dsimp only at hDec
          injection hDec with hSub
          cases tlSub with
          | mk tl htl =>
            have hListEq : hd :: tl = xs := congrArg Subtype.val hSub
            subst hListEq
            rw [FixedByteCodec.encodeElems_cons,
                hCan (bs.take n) hd (noProvBytes_take hNoProv) hHead,
                noProvCanonical_decodeChunks hCan (noProvBytes_drop hNoProv) hTail,
                list_take_append_drop_len]

theorem noProvCanonical_array {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hCan : NoProvCanonicalCodec c) (k : Nat) :
    NoProvCanonicalCodec (FixedByteCodec.array k c) :=
  fun _ _ hNoProv hDec => noProvCanonical_decodeChunks hCan hNoProv hDec

private theorem initDecoded_decodeChunks {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : InitDecodedCodec c) :
    ∀ {k : Nat} {bs : List AllocByte}
      {xs : Subtype (fun xs : List α => xs.length = k)},
      FixedByteCodec.decodeChunks c k bs = some xs → AllBytesInit bs
  | 0, [], _, _ => rfl
  | 0, _ :: _, _, hDec => by nomatch hDec
  | k + 1, bs, _, hDec => by
    rw [FixedByteCodec.decodeChunks_succ] at hDec
    cases hBle : Nat.ble n bs.length with
    | false =>
      rw [br_if_bool_false hBle] at hDec
      nomatch hDec
    | true =>
      rw [br_if_bool_true hBle] at hDec
      cases hHead : c.decode (bs.take n) with
      | none =>
        rw [hHead] at hDec
        nomatch hDec
      | some hd =>
        rw [hHead] at hDec
        cases hTail : FixedByteCodec.decodeChunks c k (bs.drop n) with
        | none =>
          rw [hTail] at hDec
          nomatch hDec
        | some _ =>
          rw [← list_take_append_drop_len n bs]
          exact AllBytesInit_append (hInit (bs.take n) hd hHead)
            (initDecoded_decodeChunks hInit hTail)

theorem initDecoded_array {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : InitDecodedCodec c) (k : Nat) :
    InitDecodedCodec (FixedByteCodec.array k c) :=
  fun _ _ hDec => initDecoded_decodeChunks hInit hDec

theorem noProvCanonical_imap {α β : Type} {n : Nat}
    {c : FixedByteCodec α n} (hCan : NoProvCanonicalCodec c)
    (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b) :
    NoProvCanonicalCodec (c.imap toβ ofβ hL hR) := by
  intro bs b hNoProv hDec
  unfold FixedByteCodec.imap FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hCDec : c.decode bs with
  | none =>
    rw [hCDec] at hDec
    nomatch hDec
  | some a =>
    rw [hCDec] at hDec
    injection hDec with hEq
    subst hEq
    change c.encode (ofβ (toβ a)) = bs
    rw [hL a]
    exact hCan bs a hNoProv hCDec

theorem initDecoded_imap {α β : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : InitDecodedCodec c)
    (toβ : α → β) (ofβ : β → α)
    (hL : ∀ a, ofβ (toβ a) = a) (hR : ∀ b, toβ (ofβ b) = b) :
    InitDecodedCodec (c.imap toβ ofβ hL hR) := by
  intro bs _ hDec
  unfold FixedByteCodec.imap FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hCDec : c.decode bs with
  | none =>
    rw [hCDec] at hDec
    nomatch hDec
  | some a => exact hInit bs a hCDec

theorem noProvCanonical_refineNiche {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hCan : NoProvCanonicalCodec c) (P : α → Bool) :
    NoProvCanonicalCodec (c.refineNiche P) := by
  intro bs sub hNoProv hDec
  unfold FixedByteCodec.refineNiche FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hCDec : c.decode bs with
  | none =>
    rw [hCDec] at hDec
    nomatch hDec
  | some a =>
    rw [hCDec] at hDec
    dsimp only at hDec
    cases hP : P a with
    | false =>
      rw [br_dite_neg (by rw [hP]; exact br_false_ne_true)] at hDec
      nomatch hDec
    | true =>
      have hSubVal : sub.val = a := by
        rw [br_dite_pos hP] at hDec
        injection hDec with hEq
        exact (congrArg Subtype.val hEq).symm
      change c.encode sub.val = bs
      rw [hSubVal]
      exact hCan bs a hNoProv hCDec

theorem initDecoded_refineNiche {α : Type} {n : Nat}
    {c : FixedByteCodec α n} (hInit : InitDecodedCodec c) (P : α → Bool) :
    InitDecodedCodec (c.refineNiche P) := by
  intro bs _ hDec
  unfold FixedByteCodec.refineNiche FixedByteCodec.ofRoundTrip at hDec
  dsimp only at hDec
  cases hCDec : c.decode bs with
  | none =>
    rw [hCDec] at hDec
    nomatch hDec
  | some a => exact hInit bs a hCDec

/-! ### 1b. Core Typed Lens & Disjoint Framing Laws -/

/-- **PutGet (`typedSubLens_get_put`):** Writing `v : α` via
`typedSubLensPut` and reading back via `typedSubLensGet` yields `some v`.
(Note: `LawfulLens.put_get` uses the functional-lens naming `put_get` for
this same write-then-read property; `TypedByteSubLens.toLens_lawful` maps
these cleanly.) -/
theorem typedSubLens_get_put {α : Type} {n : Nat}
    (l : ByteSubLens) (c : FixedByteCodec α n)
    (mem mem' : MemoryState) (v : α)
    (hPut : typedSubLensPut l c mem v = some mem') :
    typedSubLensGet l c mem' = some v := by
  unfold typedSubLensGet
  rw [byteSubLens_put_get l mem mem' (c.encode v) hPut]
  exact c.decode_encode v

/-- Constructive existence companion to `typedSubLens_get_put` directly from
`Trusted.MirSemantics.{findAllocation, isInBounds, isAligned}` preconditions
on a valid mutable aligned `[offset, offset + n)` region. -/
theorem typedSubLens_put_valid_get {α : Type} {n : Nat}
    (l : ByteSubLens) (c : FixedByteCodec α n) (mem : MemoryState)
    (a : Allocation) (v : α)
    (hPos : 0 < n) (hSize : l.size = n)
    (hFind : findAllocation l.allocId mem.allocations = some a)
    (hMut : a.mutability = .mut) (hLive : a.live = true)
    (hBounds : isInBounds a l.offset n = true)
    (hAligned : isAligned a l.offset l.alignLog2 = true) :
    ∃ mem' : MemoryState,
      typedSubLensPut l c mem v = some mem' ∧
      typedSubLensGet l c mem' = some v := by
  have hFindComp : findAllocationComp l.allocId mem.allocations = some a := by
    rw [findAllocationComp_eq]
    exact hFind
  have hBl : Nat.blt 0 l.size = true := by
    rw [hSize]
    exact (br_nat_blt_iff 0 n).mpr hPos
  have hEncLen : (c.encode v).length = l.size := by
    rw [c.encode_length v, hSize]
  have hBeq : Nat.beq (c.encode v).length l.size = true :=
    (br_nat_beq_iff _ _).mpr hEncLen
  have hNz : Nat.beq (c.encode v).length 0 = false := by
    rw [c.encode_length v]
    exact br_nat_beq_zero_false_of_lt hPos
  have hGuard :
      (!a.live || !isInBoundsComp a l.offset (c.encode v).length ||
        !isAlignedComp a l.offset l.alignLog2) = false := by
    change (!a.live || !isInBounds a l.offset (c.encode v).length ||
      !isAligned a l.offset l.alignLog2) = false
    rw [c.encode_length v, hLive, hBounds, hAligned]
    rfl
  let mem' : MemoryState :=
    { nextAllocId := mem.nextAllocId
      allocations :=
        replaceAllocationComp
          { a with
            bytes :=
              a.bytes.take l.offset ++ c.encode v ++
                a.bytes.drop (l.offset + (c.encode v).length) }
          mem.allocations }
  have hPut : typedSubLensPut l c mem v = some mem' := by
    unfold typedSubLensPut byteSubLensPut writeBytesComp
    rw [hBl, hBeq]
    dsimp only
    rw [hNz, hFindComp]
    dsimp only [br_ite_false_true]
    rw [br_if_bool_false hGuard, hMut]
    dsimp only [mem']
    rw [hMut]
    rfl
  exact ⟨mem', hPut, typedSubLens_get_put l c mem mem' v hPut⟩

/-- **GetPut (`typedSubLens_put_get`):** Under full canonicality (`c.decode bs
= some v → c.encode v = bs`), reading `some v` and writing `v` back leaves
`MemoryState` unchanged (`LawfulLens.get_put`). -/
theorem typedSubLens_put_get {α : Type} {n : Nat}
    (l : ByteSubLens) (c : FixedByteCodec α n)
    (hCan : CanonicalCodec c) (mem : MemoryState) (v : α)
    (hGet : typedSubLensGet l c mem = some v) :
    typedSubLensPut l c mem v = some mem := by
  unfold typedSubLensGet at hGet
  cases hRawGet : byteSubLensGet l mem with
  | none =>
    rw [hRawGet] at hGet
    nomatch hGet
  | some bs =>
    rw [hRawGet] at hGet
    change c.decode bs = some v at hGet
    unfold typedSubLensPut
    rw [hCan bs v hGet]
    exact byteSubLens_get_put l mem bs hRawGet

/-- **GetPut with `NoProvBytes` (`typedSubLens_put_get_noProv`):** Under
`NoProvCanonicalCodec c`, reading `some v` from a provenance-free slice and
writing `v` back leaves `MemoryState` unchanged. -/
theorem typedSubLens_put_get_noProv {α : Type} {n : Nat}
    (l : ByteSubLens) (c : FixedByteCodec α n)
    (hCan : NoProvCanonicalCodec c) (mem : MemoryState)
    (bs : List AllocByte) (v : α)
    (hRawGet : byteSubLensGet l mem = some bs)
    (hNoProv : NoProvBytes bs)
    (hDec : c.decode bs = some v) :
    typedSubLensPut l c mem v = some mem := by
  unfold typedSubLensPut
  rw [hCan bs v hNoProv hDec]
  exact byteSubLens_get_put l mem bs hRawGet

/-- **PutPut (`typedSubLens_put_put`):** Writing `v1` then `v2` through `l` and
`c` collapses to writing `v2`. -/
theorem typedSubLens_put_put {α : Type} {n : Nat}
    (l : ByteSubLens) (c : FixedByteCodec α n)
    (mem mem1 : MemoryState) (v1 v2 : α)
    (hPut1 : typedSubLensPut l c mem v1 = some mem1) :
    typedSubLensPut l c mem1 v2 = typedSubLensPut l c mem v2 :=
  byteSubLens_put_put l mem mem1 (c.encode v1) (c.encode v2) hPut1

/-- **Disjoint Frame (`typedSubLens_get_put_disjoint`):** Writing through `l1`
preserves `typedSubLensGet l2 c2` whenever `byteLensDisjoint l1 l2 = true`. -/
theorem typedSubLens_get_put_disjoint {α β : Type} {n1 n2 : Nat}
    (l1 l2 : ByteSubLens) (c1 : FixedByteCodec α n1)
    (c2 : FixedByteCodec β n2) (mem mem' : MemoryState) (v1 : α)
    (hDisj : byteLensDisjoint l1 l2 = true)
    (hPut : typedSubLensPut l1 c1 mem v1 = some mem') :
    typedSubLensGet l2 c2 mem' = typedSubLensGet l2 c2 mem := by
  unfold typedSubLensGet
  rw [byteSubLens_get_put_disjoint l1 l2 mem mem' (c1.encode v1) hDisj hPut]

/-- Every `TypedByteSubLens` with a `CanonicalCodec` forms a full
`LawfulLens MemoryState α` (`get_put`, `put_get`, `put_put`). -/
theorem TypedByteSubLens.toLens_lawful {α : Type} {n : Nat}
    (tbl : TypedByteSubLens α n) (hCan : CanonicalCodec tbl.codec) :
    LawfulLens MemoryState α tbl.toLens where
  get_put := fun mem v hGet =>
    typedSubLens_put_get tbl.lens tbl.codec hCan mem v hGet
  put_get := fun mem v mem' hPut =>
    typedSubLens_get_put tbl.lens tbl.codec mem mem' v hPut
  put_put := fun mem v1 v2 mem1 hPut1 =>
    typedSubLens_put_put tbl.lens tbl.codec mem mem1 v1 v2 hPut1

/-! ### 1c. Adjacent Struct-Field `prod` Decomposition -/

/-- Geometric and alignment compatibility for splitting a parent byte lens
`l12` (`[off, off + n1 + n2)`) into two contiguous field sub-lenses
`l1` (`[off, off + n1)`) and `l2` (`[off + n1, off + n1 + n2)`). -/
structure AdjacentSubLenses (l1 l2 l12 : ByteSubLens) (n1 n2 : Nat) :
    Prop where
  pos1 : 0 < n1
  pos2 : 0 < n2
  allocId12 : l12.allocId = l1.allocId
  allocId2 : l2.allocId = l1.allocId
  offset1 : l1.offset = l12.offset
  offset2 : l2.offset = l12.offset + n1
  size1 : l1.size = n1
  size2 : l2.size = n2
  size12 : l12.size = n1 + n2
  align1_le : l1.alignLog2 ≤ l12.alignLog2
  align2_le : l2.alignLog2 ≤ l12.alignLog2
  n1_aligned : Nat.mod n1 (Nat.pow 2 l2.alignLog2) = 0

/-- Forward split-borrow field assembly: whenever writing `(v1, v2)` via
`FixedByteCodec.prod c1 c2` on parent `l12` succeeds (`= some mem'`), writing
`v1` on `l1` followed by `v2` on `l2` succeeds with the exact same
`MemoryState` `mem'`. -/
theorem typedSubLensPut_prod_forward {α β : Type} {n1 n2 : Nat}
    (l1 l2 l12 : ByteSubLens) (c1 : FixedByteCodec α n1)
    (c2 : FixedByteCodec β n2)
    (hAdj : AdjacentSubLenses l1 l2 l12 n1 n2)
    (mem mem' : MemoryState) (v1 : α) (v2 : β)
    (hPut :
      typedSubLensPut l12 (FixedByteCodec.prod c1 c2) mem (v1, v2) =
        some mem') :
    (typedSubLensPut l1 c1 mem v1).bind
        (fun m1 => typedSubLensPut l2 c2 m1 v2) = some mem' := by
  have hAid12 := hAdj.allocId12
  have hAid2 := hAdj.allocId2
  have hOff1 := hAdj.offset1
  have hOff2 := hAdj.offset2
  have hSz1 := hAdj.size1
  have hSz2 := hAdj.size2
  have hSz12 := hAdj.size12
  have hPos12 : 0 < n1 + n2 := br_nat_add_pos_left hAdj.pos1 n2
  have hEncLen12 :
      ((FixedByteCodec.prod c1 c2).encode (v1, v2)).length = l12.size := by
    rw [FixedByteCodec.encode_length, hSz12]
  have hEncLen1 : (c1.encode v1).length = l1.size := by
    rw [c1.encode_length v1, hSz1]
  have hEncLen2 : (c2.encode v2).length = l2.size := by
    rw [c2.encode_length v2, hSz2]
  unfold typedSubLensPut byteSubLensPut at hPut
  rw [hSz12, (br_nat_blt_iff 0 (n1 + n2)).mpr hPos12,
      (br_nat_beq_iff _ _).mpr
        (by rw [FixedByteCodec.encode_length])] at hPut
  dsimp only [writeBytesComp] at hPut
  rw [FixedByteCodec.prod_encode_eq, List.length_append, c1.encode_length,
      c2.encode_length, br_nat_beq_zero_false_of_lt hPos12] at hPut
  dsimp only [br_ite_false_true] at hPut
  cases hFind : findAllocationComp l12.allocId mem.allocations with
  | none =>
    rw [hFind] at hPut
    nomatch hPut
  | some a =>
    rw [hFind] at hPut
    dsimp only at hPut
    cases hGuard : (!a.live || !isInBoundsComp a l12.offset (n1 + n2) ||
        !isAlignedComp a l12.offset l12.alignLog2) with
    | true =>
      rw [br_if_bool_true hGuard] at hPut
      nomatch hPut
    | false =>
      rw [br_if_bool_false hGuard] at hPut
      have hG1 := br_bor_false hGuard
      have hG2 := br_bor_false hG1.1
      have hLive : a.live = true := by
        cases hl : a.live with
        | true => rfl
        | false => rw [hl] at hG2; nomatch hG2.1
      have hBounds12 : isInBoundsComp a l12.offset (n1 + n2) = true := by
        cases hb : isInBoundsComp a l12.offset (n1 + n2) with
        | true => rfl
        | false => rw [hb] at hG2; nomatch hG2.2
      have hAl12 : isAlignedComp a l12.offset l12.alignLog2 = true := by
        cases ha : isAlignedComp a l12.offset l12.alignLog2 with
        | true => rfl
        | false => rw [ha] at hG1; nomatch hG1.2
      cases hMutB : mutabilityIsMut a.mutability with
      | false =>
        have hMut := br_mutability_eq_shared a.mutability hMutB
        rw [hMut] at hPut
        nomatch hPut
      | true =>
        have hMut := br_mutability_eq_mut a.mutability hMutB
        rw [hMut] at hPut
        injection hPut with hMemEq
        have hFind1 : findAllocationComp l1.allocId mem.allocations = some a := by
          rw [← hAid12]; exact hFind
        have hFindId : a.allocId = l1.allocId :=
          findAllocationComp_allocId l1.allocId mem.allocations a hFind1
        have hBounds1 : isInBoundsComp a l1.offset n1 = true := by
          dsimp only [isInBoundsComp] at hBounds12
          have hLe12 : l12.offset + (n1 + n2) ≤ a.bytes.length :=
            (br_nat_ble_iff _ _).mp hBounds12
          have hLe1 : l1.offset + n1 ≤ a.bytes.length := by
            rw [hOff1]
            exact Nat.le_trans
              (Nat.add_le_add_left (Nat.le_add_right n1 n2) l12.offset) hLe12
          exact (br_nat_ble_iff _ _).mpr hLe1
        have hAl1 : isAlignedComp a l1.offset l1.alignLog2 = true := by
          rw [hOff1]
          exact isAlignedComp_of_le a l12.offset l1.alignLog2 l12.alignLog2
            hAdj.align1_le hAl12
        have hG1False :
            (!a.live || !isInBoundsComp a l1.offset (c1.encode v1).length ||
              !isAlignedComp a l1.offset l1.alignLog2) = false := by
          rw [c1.encode_length, hLive, hBounds1, hAl1]; rfl
        let a1 : Allocation :=
          { a with
            bytes :=
              a.bytes.take l1.offset ++ c1.encode v1 ++
                a.bytes.drop (l1.offset + (c1.encode v1).length) }
        let m1 : MemoryState :=
          { nextAllocId := mem.nextAllocId
            allocations := replaceAllocationComp a1 mem.allocations }
        have hPut1 : typedSubLensPut l1 c1 mem v1 = some m1 := by
          unfold typedSubLensPut byteSubLensPut writeBytesComp
          rw [hSz1, (br_nat_blt_iff 0 n1).mpr hAdj.pos1,
              (br_nat_beq_iff _ _).mpr (c1.encode_length v1),
              c1.encode_length, br_nat_beq_zero_false_of_lt hAdj.pos1,
              hFind1]
          dsimp only [br_ite_false_true]
          rw [c1.encode_length] at hG1False
          rw [br_if_bool_false hG1False, hMut]
          dsimp only [m1, a1]
          rw [c1.encode_length, hMut]
          rfl
        have hFind2 : findAllocationComp l2.allocId m1.allocations = some a1 := by
          dsimp only [m1]
          rw [hAid2, ← hFindId]
          exact findAllocationComp_replace_same mem.allocations a a1
            (by rw [hFindId]; exact hFind1) rfl
        have hBounds12' : l12.offset + (n1 + n2) ≤ a.bytes.length :=
          (br_nat_ble_iff _ _).mp hBounds12
        have hLen1 : a1.bytes.length = a.bytes.length := by
          dsimp only [a1]
          exact br_splice_length l1.offset (c1.encode v1) a.bytes
            (by rw [c1.encode_length, hOff1]
                exact Nat.le_trans
                  (Nat.add_le_add_left (Nat.le_add_right n1 n2) l12.offset)
                  hBounds12')
        have hBounds2 : isInBoundsComp a1 l2.offset n2 = true := by
          dsimp only [isInBoundsComp]
          rw [hLen1, hOff2, Nat.add_assoc]
          exact hBounds12
        have hAl2 : isAlignedComp a1 l2.offset l2.alignLog2 = true := by
          dsimp only [a1]
          change isAlignedComp a l2.offset l2.alignLog2 = true
          rw [hOff2]
          exact isAlignedComp_add a l12.offset n1 l12.alignLog2 l2.alignLog2
            hAdj.align2_le hAdj.n1_aligned hAl12
        have hG2False :
            (!a1.live || !isInBoundsComp a1 l2.offset (c2.encode v2).length ||
              !isAlignedComp a1 l2.offset l2.alignLog2) = false := by
          rw [c2.encode_length]
          change (!a.live || !isInBoundsComp a1 l2.offset n2 ||
            !isAlignedComp a1 l2.offset l2.alignLog2) = false
          rw [hLive, hBounds2, hAl2]
          rfl
        have hBytesEq :
            a1.bytes.take l2.offset ++ c2.encode v2 ++
                a1.bytes.drop (l2.offset + (c2.encode v2).length) =
              a.bytes.take l12.offset ++ (c1.encode v1 ++ c2.encode v2) ++
                a.bytes.drop (l12.offset + (n1 + n2)) := by
          dsimp only [a1]
          rw [hOff1, hOff2, c1.encode_length, c2.encode_length]
          have hSp :=
            br_splice_adjacent_eq l12.offset (c1.encode v1) (c2.encode v2)
              a.bytes
              (by rw [c1.encode_length, c2.encode_length]; exact hBounds12')
          rw [c1.encode_length, c2.encode_length] at hSp
          exact hSp
        rw [hPut1]
        dsimp only [Option.bind]
        unfold typedSubLensPut byteSubLensPut writeBytesComp
        rw [hSz2, (br_nat_blt_iff 0 n2).mpr hAdj.pos2,
            (br_nat_beq_iff _ _).mpr (c2.encode_length v2),
            c2.encode_length, br_nat_beq_zero_false_of_lt hAdj.pos2]
        dsimp only [br_ite_false_true]
        rw [hFind2]
        dsimp only
        rw [c2.encode_length] at hG2False
        rw [br_if_bool_false hG2False, hMut]
        dsimp only
        dsimp only [m1, a1]
        rw [c2.encode_length] at hBytesEq
        rw [hBytesEq]
        have hRepEq := replaceAllocationComp_replace_same mem.allocations a1
          { allocId := a.allocId
            alignLog2 := a.alignLog2
            mutability := .mut
            bytes := a.bytes.take l12.offset ++ (c1.encode v1 ++ c2.encode v2) ++
              a.bytes.drop (l12.offset + (n1 + n2))
            live := a.live }
          rfl
        rw [hRepEq, ← hMemEq]
        rfl

/-- Unconditional equational split-borrow field assembly when the parent's
alignment does not exceed field 1's (`l12.alignLog2 ≤ l1.alignLog2`, covering
byte-aligned parents `l12.alignLog2 = 0` and descending alignments such as
`(u32, u16)` or `(u32, u8)`): writing `(v1, v2)` via `prod c1 c2` on `l12`
equals writing `v1` on `l1` then `v2` on `l2` on every `MemoryState`. -/
theorem typedSubLensPut_prod_eq_seq {α β : Type} {n1 n2 : Nat}
    (l1 l2 l12 : ByteSubLens) (c1 : FixedByteCodec α n1)
    (c2 : FixedByteCodec β n2)
    (hAdj : AdjacentSubLenses l1 l2 l12 n1 n2)
    (hAlParent : l12.alignLog2 ≤ l1.alignLog2)
    (mem : MemoryState) (v1 : α) (v2 : β) :
    typedSubLensPut l12 (FixedByteCodec.prod c1 c2) mem (v1, v2) =
      (typedSubLensPut l1 c1 mem v1).bind
        (fun m1 => typedSubLensPut l2 c2 m1 v2) := by
  have hAlEq : l12.alignLog2 = l1.alignLog2 :=
    Nat.le_antisymm hAlParent hAdj.align1_le
  have hPos12 : 0 < n1 + n2 := br_nat_add_pos_left hAdj.pos1 n2
  unfold typedSubLensPut byteSubLensPut writeBytesComp
  rw [hAdj.size12, hAdj.size1,
      (br_nat_blt_iff 0 (n1 + n2)).mpr hPos12,
      (br_nat_blt_iff 0 n1).mpr hAdj.pos1,
      (br_nat_beq_iff _ _).mpr
        (by rw [FixedByteCodec.encode_length]),
      (br_nat_beq_iff _ _).mpr (c1.encode_length v1),
      FixedByteCodec.prod_encode_eq, List.length_append,
      c1.encode_length, c2.encode_length,
      br_nat_beq_zero_false_of_lt hPos12,
      br_nat_beq_zero_false_of_lt hAdj.pos1]
  dsimp only [br_ite_false_true]
  rw [hAdj.allocId12, hAdj.offset1, hAlEq]
  cases hFind : findAllocationComp l1.allocId mem.allocations with
  | none => rfl
  | some a =>
    dsimp only
    cases hLive : a.live with
    | false =>
      have hT12 : (!false || !isInBoundsComp a l12.offset (n1 + n2) ||
          !isAlignedComp a l12.offset l1.alignLog2) = true := rfl
      have hT1 : (!false || !isInBoundsComp a l12.offset n1 ||
          !isAlignedComp a l12.offset l1.alignLog2) = true := rfl
      rw [br_if_bool_true hT12, br_if_bool_true hT1]
      rfl
    | true =>
      cases hAl1 : isAlignedComp a l12.offset l1.alignLog2 with
      | false =>
        have hT12 : (!true || !isInBoundsComp a l12.offset (n1 + n2) ||
            !false) = true := by
          cases isInBoundsComp a l12.offset (n1 + n2) <;> rfl
        have hT1 : (!true || !isInBoundsComp a l12.offset n1 ||
            !false) = true := by
          cases isInBoundsComp a l12.offset n1 <;> rfl
        rw [br_if_bool_true hT12, br_if_bool_true hT1]
        rfl
      | true =>
        cases hB12 : isInBoundsComp a l12.offset (n1 + n2) with
        | true =>
          cases hMutB : mutabilityIsMut a.mutability with
          | false =>
            have hMut := br_mutability_eq_shared a.mutability hMutB
            have hB1 : isInBoundsComp a l12.offset n1 = true := by
              dsimp only [isInBoundsComp] at hB12
              exact (br_nat_ble_iff _ _).mpr (Nat.le_trans
                (Nat.add_le_add_left (Nat.le_add_right n1 n2) l12.offset)
                ((br_nat_ble_iff _ _).mp hB12))
            have hF12 : (!true || !true || !true) = false := rfl
            rw [br_if_bool_false hF12, hMut, hB1, br_if_bool_false hF12]
            rfl
          | true =>
            have hMut := br_mutability_eq_mut a.mutability hMutB
            let a12 : Allocation :=
              { allocId := a.allocId
                alignLog2 := a.alignLog2
                mutability := .mut
                bytes :=
                  a.bytes.take l12.offset ++
                    (c1.encode v1 ++ c2.encode v2) ++
                    a.bytes.drop (l12.offset + (n1 + n2))
                live := true }
            let target : MemoryState :=
              { nextAllocId := mem.nextAllocId
                allocations := replaceAllocationComp a12 mem.allocations }
            have hPut12 :
                typedSubLensPut l12 (FixedByteCodec.prod c1 c2) mem (v1, v2) =
                  some target := by
              unfold typedSubLensPut byteSubLensPut writeBytesComp
              rw [hAdj.size12, (br_nat_blt_iff 0 (n1 + n2)).mpr hPos12,
                  (br_nat_beq_iff _ _).mpr
                    (by rw [FixedByteCodec.encode_length]),
                  FixedByteCodec.prod_encode_eq, List.length_append,
                  c1.encode_length, c2.encode_length,
                  br_nat_beq_zero_false_of_lt hPos12]
              dsimp only [br_ite_false_true]
              rw [hAdj.allocId12, hFind]
              dsimp only
              have hF12 : (!true || !true || !true) = false := rfl
              rw [hB12, hAlEq, hAl1, hLive, br_if_bool_false hF12, hMut]
              rfl
            have hFwd :=
              typedSubLensPut_prod_forward l1 l2 l12 c1 c2 hAdj mem target
                v1 v2 hPut12
            have hB1 : isInBoundsComp a l12.offset n1 = true := by
              dsimp only [isInBoundsComp] at hB12
              exact (br_nat_ble_iff _ _).mpr (Nat.le_trans
                (Nat.add_le_add_left (Nat.le_add_right n1 n2) l12.offset)
                ((br_nat_ble_iff _ _).mp hB12))
            let a1 : Allocation :=
              { allocId := a.allocId
                alignLog2 := a.alignLog2
                mutability := .mut
                bytes :=
                  a.bytes.take l12.offset ++ c1.encode v1 ++
                    a.bytes.drop (l12.offset + n1)
                live := true }
            let m1 : MemoryState :=
              { nextAllocId := mem.nextAllocId
                allocations := replaceAllocationComp a1 mem.allocations }
            have hPut1Eq : typedSubLensPut l1 c1 mem v1 = some m1 := by
              unfold typedSubLensPut byteSubLensPut writeBytesComp
              rw [hAdj.size1, (br_nat_blt_iff 0 n1).mpr hAdj.pos1,
                  (br_nat_beq_iff _ _).mpr (c1.encode_length v1),
                  c1.encode_length, br_nat_beq_zero_false_of_lt hAdj.pos1]
              dsimp only [br_ite_false_true]
              rw [hFind]
              dsimp only
              have hF1 : (!true || !true || !true) = false := rfl
              rw [hLive, hAdj.offset1, hB1, hAl1, br_if_bool_false hF1, hMut]
              rfl
            rw [hPut1Eq] at hFwd
            dsimp only [Option.bind] at hFwd
            unfold typedSubLensPut byteSubLensPut writeBytesComp at hFwd
            rw [c2.encode_length] at hFwd
            dsimp only at hFwd
            have hF12 : (!true || !true || !true) = false := rfl
            rw [br_if_bool_false hF12, hMut, hB1, br_if_bool_false hF12]
            dsimp only
            exact hFwd.symm
        | false =>
          have hNot12 : ¬ (l12.offset + (n1 + n2) ≤ a.bytes.length) := by
            intro hLe
            dsimp only [isInBoundsComp] at hB12
            rw [(br_nat_ble_iff _ _).mpr hLe] at hB12
            nomatch hB12
          have hT12 : (!true || !false || !true) = true := rfl
          rw [br_if_bool_true hT12]
          cases hB1 : isInBoundsComp a l12.offset n1 with
          | false =>
            have hT1 : (!true || !false || !true) = true := rfl
            rw [br_if_bool_true hT1]
            rfl
          | true =>
            have hF1 : (!true || !true || !true) = false := rfl
            rw [br_if_bool_false hF1]
            cases hMutB : mutabilityIsMut a.mutability with
            | false =>
              have hMut := br_mutability_eq_shared a.mutability hMutB
              rw [hMut]
              rfl
            | true =>
              have hMut := br_mutability_eq_mut a.mutability hMutB
              rw [hMut]
              have hTT : (true && true) = true := rfl
              rw [hTT]
              dsimp only [Option.bind]
              let a1 : Allocation :=
                { allocId := a.allocId
                  alignLog2 := a.alignLog2
                  mutability := .mut
                  bytes :=
                    a.bytes.take l12.offset ++ c1.encode v1 ++
                      a.bytes.drop (l12.offset + n1)
                  live := true }
              have hId1 : a.allocId = l1.allocId :=
                findAllocationComp_allocId l1.allocId mem.allocations a hFind
              have hFind1 :
                  findAllocationComp l2.allocId
                    (replaceAllocationComp a1 mem.allocations) = some a1 := by
                rw [hAdj.allocId2, ← hId1]
                exact findAllocationComp_replace_same mem.allocations a a1
                  (by rw [hId1]; exact hFind) rfl
              have hLenA1 : a1.bytes.length = a.bytes.length := by
                dsimp only [a1]
                have hSp :=
                  br_splice_length l12.offset (c1.encode v1) a.bytes
                    (by rw [c1.encode_length]
                        exact (br_nat_ble_iff _ _).mp hB1)
                rw [c1.encode_length] at hSp
                exact hSp
              have hB2False : isInBoundsComp a1 l2.offset n2 = false := by
                dsimp only [isInBoundsComp]
                rw [hLenA1, hAdj.offset2]
                cases hCb : Nat.ble (l12.offset + n1 + n2) a.bytes.length with
                | false => rfl
                | true =>
                  have hLe := (br_nat_ble_iff _ _).mp hCb
                  rw [Nat.add_assoc] at hLe
                  exact False.elim (hNot12 hLe)
              rw [hAdj.size2, (br_nat_blt_iff 0 n2).mpr hAdj.pos2,
                  br_nat_beq_refl n2, br_nat_beq_zero_false_of_lt hAdj.pos2,
                  hFind1]
              dsimp only [br_ite_false_true]
              rw [hB2False]
              have hT2 : (!a1.live || !false ||
                  !isAlignedComp a1 l2.offset l2.alignLog2) = true := by
                cases a1.live <;> cases isAlignedComp a1 l2.offset l2.alignLog2 <;> rfl
              rw [br_if_bool_true hT2]
              rfl

/-- Unconditional `prod` read decomposition when `l12.alignLog2 ≤ l1.alignLog2`:
reading `l12` via `prod c1 c2` yields `some (v1, v2)` iff reading `l1` via
`c1` yields `some v1` and reading `l2` via `c2` yields `some v2`. -/
theorem typedSubLensGet_prod_eq {α β : Type} {n1 n2 : Nat}
    (l1 l2 l12 : ByteSubLens) (c1 : FixedByteCodec α n1)
    (c2 : FixedByteCodec β n2)
    (hAdj : AdjacentSubLenses l1 l2 l12 n1 n2)
    (hAlParent : l12.alignLog2 ≤ l1.alignLog2)
    (mem : MemoryState) :
    typedSubLensGet l12 (FixedByteCodec.prod c1 c2) mem =
      match typedSubLensGet l1 c1 mem, typedSubLensGet l2 c2 mem with
      | some v1, some v2 => some (v1, v2)
      | _, _ => none := by
  have hAlEq : l12.alignLog2 = l1.alignLog2 :=
    Nat.le_antisymm hAlParent hAdj.align1_le
  have hPos12 : 0 < n1 + n2 := br_nat_add_pos_left hAdj.pos1 n2
  unfold typedSubLensGet byteSubLensGet readBytesComp
  rw [hAdj.size12, hAdj.size1, hAdj.size2,
      (br_nat_blt_iff 0 (n1 + n2)).mpr hPos12,
      (br_nat_blt_iff 0 n1).mpr hAdj.pos1,
      (br_nat_blt_iff 0 n2).mpr hAdj.pos2,
      br_nat_beq_zero_false_of_lt hPos12,
      br_nat_beq_zero_false_of_lt hAdj.pos1,
      br_nat_beq_zero_false_of_lt hAdj.pos2,
      hAdj.allocId12, hAdj.allocId2, hAdj.offset1, hAdj.offset2, hAlEq]
  dsimp only [br_ite_false_true]
  cases hFind : findAllocationComp l1.allocId mem.allocations with
  | none => rfl
  | some a =>
    dsimp only
    cases mutabilityIsMut a.mutability with
    | false => rfl
    | true =>
      cases hLive : a.live with
      | false =>
        have hT12 : (!false || !isInBoundsComp a l12.offset (n1 + n2) ||
            !isAlignedComp a l12.offset l1.alignLog2) = true := rfl
        have hT1 : (!false || !isInBoundsComp a l12.offset n1 ||
            !isAlignedComp a l12.offset l1.alignLog2) = true := rfl
        rw [br_if_bool_true hT12, br_if_bool_true hT1]
        rfl
      | true =>
        cases hAl1 : isAlignedComp a l12.offset l1.alignLog2 with
        | false =>
          have hT12 : (!true || !isInBoundsComp a l12.offset (n1 + n2) ||
              !false) = true := by
            cases isInBoundsComp a l12.offset (n1 + n2) <;> rfl
          have hT1 : (!true || !isInBoundsComp a l12.offset n1 ||
              !false) = true := by
            cases isInBoundsComp a l12.offset n1 <;> rfl
          rw [br_if_bool_true hT12, br_if_bool_true hT1]
          rfl
        | true =>
          have hAl1Full : isAlignedComp a l12.offset l1.alignLog2 = true := hAl1
          rw [← hAlEq] at hAl1Full
          have hAl2 :=
            isAlignedComp_add a l12.offset n1 l12.alignLog2 l2.alignLog2
              hAdj.align2_le hAdj.n1_aligned hAl1Full
          cases hB12 : isInBoundsComp a l12.offset (n1 + n2) with
          | false =>
            have hNot12 : ¬ (l12.offset + (n1 + n2) ≤ a.bytes.length) := by
              intro hLe
              dsimp only [isInBoundsComp] at hB12
              rw [(br_nat_ble_iff _ _).mpr hLe] at hB12
              nomatch hB12
            have hT12 : (!true || !false || !true) = true := rfl
            rw [br_if_bool_true hT12]
            cases hB1 : isInBoundsComp a l12.offset n1 with
            | false =>
              have hT1 : (!true || !false || !true) = true := rfl
              rw [br_if_bool_true hT1]
              rfl
            | true =>
              have hF1 : (!true || !true || !true) = false := rfl
              have hB2False : isInBoundsComp a (l12.offset + n1) n2 = false := by
                dsimp only [isInBoundsComp]
                cases hCb : Nat.ble (l12.offset + n1 + n2) a.bytes.length with
                | false => rfl
                | true =>
                  have hLe := (br_nat_ble_iff _ _).mp hCb
                  rw [Nat.add_assoc] at hLe
                  exact False.elim (hNot12 hLe)
              have hT2 : (!true || !false || !true) = true := rfl
              rw [br_if_bool_false hF1, hB2False, hAl2, br_if_bool_true hT2]
              dsimp only [Option.bind]
              cases c1.decode ((a.bytes.drop l12.offset).take n1) <;> rfl
          | true =>
            have hLe12 : l12.offset + (n1 + n2) ≤ a.bytes.length :=
              (br_nat_ble_iff _ _).mp hB12
            have hB1 : isInBoundsComp a l12.offset n1 = true := by
              dsimp only [isInBoundsComp]
              exact (br_nat_ble_iff _ _).mpr (Nat.le_trans
                (Nat.add_le_add_left (Nat.le_add_right n1 n2) l12.offset) hLe12)
            have hB2 : isInBoundsComp a (l12.offset + n1) n2 = true := by
              dsimp only [isInBoundsComp]
              rw [Nat.add_assoc]
              exact hB12
            have hF : (!true || !true || !true) = false := rfl
            rw [hB1, hB2, hAl2, br_if_bool_false hF, br_if_bool_false hF,
                br_if_bool_false hF]
            dsimp only [Option.bind]
            let full := (a.bytes.drop l12.offset).take (n1 + n2)
            have hFullLen : full.length = n1 + n2 := by
              dsimp only [full]
              apply br_length_take_of_le
              rw [br_length_drop]
              exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hLe12)
            have hBeqFull : Nat.beq full.length (n1 + n2) = true :=
              (br_nat_beq_iff _ _).mpr hFullLen
            change
              (FixedByteCodec.prod c1 c2).decode full =
                match c1.decode ((a.bytes.drop l12.offset).take n1),
                    c2.decode ((a.bytes.drop (l12.offset + n1)).take n2) with
                | some v1, some v2 => some (v1, v2)
                | _, _ => none
            unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
            dsimp only
            rw [br_if_bool_true hBeqFull,
                list_drop_take_adjacent_fst l12.offset n1 n2 a.bytes,
                list_drop_take_adjacent_snd l12.offset n1 n2 a.bytes]
            cases c1.decode ((a.bytes.drop l12.offset).take n1) with
            | none => rfl
            | some v1 =>
              cases c2.decode ((a.bytes.drop (l12.offset + n1)).take n2) <;> rfl

/-- `↔` form of `typedSubLensGet_prod_eq` allowing ascending child alignment
(`l12.alignLog2 > l1.alignLog2`, e.g. `(u16, u32)`) whenever `mem`'s allocation
is aligned at parent `l12.alignLog2`. -/
theorem typedSubLensGet_prod_of_parent_aligned {α β : Type} {n1 n2 : Nat}
    (l1 l2 l12 : ByteSubLens) (c1 : FixedByteCodec α n1)
    (c2 : FixedByteCodec β n2)
    (hAdj : AdjacentSubLenses l1 l2 l12 n1 n2)
    (mem : MemoryState)
    (hParentAligned :
      ∀ a, findAllocation l12.allocId mem.allocations = some a →
        isAligned a l12.offset l12.alignLog2 = true) :
    typedSubLensGet l12 (FixedByteCodec.prod c1 c2) mem =
      match typedSubLensGet l1 c1 mem, typedSubLensGet l2 c2 mem with
      | some v1, some v2 => some (v1, v2)
      | _, _ => none := by
  have hPos12 : 0 < n1 + n2 := br_nat_add_pos_left hAdj.pos1 n2
  unfold typedSubLensGet byteSubLensGet readBytesComp
  rw [hAdj.size12, hAdj.size1, hAdj.size2,
      (br_nat_blt_iff 0 (n1 + n2)).mpr hPos12,
      (br_nat_blt_iff 0 n1).mpr hAdj.pos1,
      (br_nat_blt_iff 0 n2).mpr hAdj.pos2,
      br_nat_beq_zero_false_of_lt hPos12,
      br_nat_beq_zero_false_of_lt hAdj.pos1,
      br_nat_beq_zero_false_of_lt hAdj.pos2,
      hAdj.allocId12, hAdj.allocId2, hAdj.offset1, hAdj.offset2]
  dsimp only [br_ite_false_true]
  cases hFind : findAllocationComp l1.allocId mem.allocations with
  | none => rfl
  | some a =>
    dsimp only
    have hFindMir : findAllocation l12.allocId mem.allocations = some a := by
      rw [← findAllocationComp_eq, hAdj.allocId12]
      exact hFind
    have hAl12 : isAlignedComp a l12.offset l12.alignLog2 = true :=
      hParentAligned a hFindMir
    have hAl1 : isAlignedComp a l12.offset l1.alignLog2 = true :=
      isAlignedComp_of_le a l12.offset l1.alignLog2 l12.alignLog2
        hAdj.align1_le hAl12
    have hAl2 : isAlignedComp a (l12.offset + n1) l2.alignLog2 = true :=
      isAlignedComp_add a l12.offset n1 l12.alignLog2 l2.alignLog2
        hAdj.align2_le hAdj.n1_aligned hAl12
    cases mutabilityIsMut a.mutability with
    | false => rfl
    | true =>
      cases hLive : a.live with
      | false =>
        have hT12 : (!false || !isInBoundsComp a l12.offset (n1 + n2) ||
            !isAlignedComp a l12.offset l12.alignLog2) = true := rfl
        have hT1 : (!false || !isInBoundsComp a l12.offset n1 ||
            !isAlignedComp a l12.offset l1.alignLog2) = true := rfl
        rw [br_if_bool_true hT12, br_if_bool_true hT1]
        rfl
      | true =>
        rw [hAl12, hAl1, hAl2]
        cases hB12 : isInBoundsComp a l12.offset (n1 + n2) with
        | false =>
          have hNot12 : ¬ (l12.offset + (n1 + n2) ≤ a.bytes.length) := by
            intro hLe
            dsimp only [isInBoundsComp] at hB12
            rw [(br_nat_ble_iff _ _).mpr hLe] at hB12
            nomatch hB12
          have hT : (!true || !false || !true) = true := rfl
          have hF : (!true || !true || !true) = false := rfl
          rw [br_if_bool_true hT]
          cases hB1 : isInBoundsComp a l12.offset n1 with
          | false => rw [br_if_bool_true hT]; rfl
          | true =>
            have hB2False : isInBoundsComp a (l12.offset + n1) n2 = false := by
              dsimp only [isInBoundsComp]
              cases hCb : Nat.ble (l12.offset + n1 + n2) a.bytes.length with
              | false => rfl
              | true =>
                have hLe := (br_nat_ble_iff _ _).mp hCb
                rw [Nat.add_assoc] at hLe
                exact False.elim (hNot12 hLe)
            rw [br_if_bool_false hF, hB2False, br_if_bool_true hT]
            dsimp only [Option.bind]
            cases c1.decode ((a.bytes.drop l12.offset).take n1) <;> rfl
        | true =>
          have hLe12 : l12.offset + (n1 + n2) ≤ a.bytes.length :=
            (br_nat_ble_iff _ _).mp hB12
          have hB1 : isInBoundsComp a l12.offset n1 = true := by
            dsimp only [isInBoundsComp]
            exact (br_nat_ble_iff _ _).mpr (Nat.le_trans
              (Nat.add_le_add_left (Nat.le_add_right n1 n2) l12.offset) hLe12)
          have hB2 : isInBoundsComp a (l12.offset + n1) n2 = true := by
            dsimp only [isInBoundsComp]
            rw [Nat.add_assoc]
            exact hB12
          have hF : (!true || !true || !true) = false := rfl
          rw [hB1, hB2, br_if_bool_false hF, br_if_bool_false hF,
              br_if_bool_false hF]
          dsimp only [Option.bind]
          let full := (a.bytes.drop l12.offset).take (n1 + n2)
          have hFullLen : full.length = n1 + n2 := by
            dsimp only [full]
            apply br_length_take_of_le
            rw [br_length_drop]
            exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hLe12)
          have hBeqFull : Nat.beq full.length (n1 + n2) = true :=
            (br_nat_beq_iff _ _).mpr hFullLen
          change
            (FixedByteCodec.prod c1 c2).decode full =
              match c1.decode ((a.bytes.drop l12.offset).take n1),
                  c2.decode ((a.bytes.drop (l12.offset + n1)).take n2) with
              | some v1, some v2 => some (v1, v2)
              | _, _ => none
          unfold FixedByteCodec.prod FixedByteCodec.ofRoundTrip
          dsimp only
          rw [br_if_bool_true hBeqFull,
              list_drop_take_adjacent_fst l12.offset n1 n2 a.bytes,
              list_drop_take_adjacent_snd l12.offset n1 n2 a.bytes]
          cases c1.decode ((a.bytes.drop l12.offset).take n1) with
          | none => rfl
          | some v1 =>
            cases c2.decode ((a.bytes.drop (l12.offset + n1)).take n2) <;> rfl

/-! ### 1d. In-Place `CodecTransmuteSound` & Fail-Closed `.uninit` Padding -/

/-- In-place `MemoryState` `CodecTransmuteSound` view cast: writing `v : α`
through `cSrc` at `l` guarantees `typedSubLensGet l cDst mem'` returns `some w`
with `cDst.encode` / `cSrc.encode` compatibility. -/
theorem typedSubLens_transmute_sound {α β : Type} {n : Nat}
    (l : ByteSubLens) (cSrc : FixedByteCodec α n)
    (cDst : FixedByteCodec β n)
    (hSound : CodecTransmuteSound cSrc cDst)
    (mem mem' : MemoryState) (v : α)
    (hPut : typedSubLensPut l cSrc mem v = some mem') :
    ∃ w : β, typedSubLensGet l cDst mem' = some w := by
  have ⟨_, w, hw⟩ := hSound v
  refine ⟨w, ?_⟩
  unfold typedSubLensGet
  rw [byteSubLens_put_get l mem mem' (cSrc.encode v) hPut]
  exact hw

/-- Trait-based corollary of `typedSubLens_transmute_sound` from `IsInitCodec` +
`NoProvCodec` + `IsSurjectiveInitDecoder`. -/
theorem typedSubLens_transmute_of_traits {α β : Type} {n : Nat}
    (l : ByteSubLens) (cSrc : FixedByteCodec α n)
    (cDst : FixedByteCodec β n)
    (hInit : cSrc.IsInitCodec) (hNoProv : cSrc.NoProvCodec)
    (hSurj : cDst.IsSurjectiveInitDecoder)
    (mem mem' : MemoryState) (v : α)
    (hPut : typedSubLensPut l cSrc mem v = some mem') :
    ∃ w : β, typedSubLensGet l cDst mem' = some w :=
  typedSubLens_transmute_sound l cSrc cDst
    (codecTransmute_sound cSrc cDst hInit hNoProv hSurj) mem mem' v hPut

/-- Because `(FixedByteCodec.padRight cSrc pad).encode v` carries `.uninit`
padding bytes whenever `0 < pad`, reading back through any
`InitDecodedCodec cDst` (such as `uintBvCodec` or `array` over initialized
primitives) returns `none` fail-closed. -/
theorem typedSubLens_padRight_init_decode_none {α β : Type} {n pad : Nat}
    (l : ByteSubLens) (cSrc : FixedByteCodec α n)
    (cDst : FixedByteCodec β (n + pad)) (hPos : 0 < pad)
    (hInitDec : InitDecodedCodec cDst) (mem mem' : MemoryState) (v : α)
    (hPut :
      typedSubLensPut l (FixedByteCodec.padRight cSrc pad) mem v = some mem') :
    typedSubLensGet l cDst mem' = none := by
  unfold typedSubLensGet
  rw [byteSubLens_put_get l mem mem'
    ((FixedByteCodec.padRight cSrc pad).encode v) hPut]
  dsimp only [Option.bind]
  cases hDec : cDst.decode ((FixedByteCodec.padRight cSrc pad).encode v) with
  | none => rfl
  | some w =>
    have hInit :
        AllBytesInit ((FixedByteCodec.padRight cSrc pad).encode v) :=
      hInitDec _ w hDec
    change allBytesInit
      ((FixedByteCodec.padRight cSrc pad).encode v) = true at hInit
    rw [FixedByteCodec.allBytesInit_padRight_encode_eq_false cSrc hPos v]
      at hInit
    nomatch hInit

theorem typedSubLens_padRight_uintBvCodec_none {α : Type} {n pad : Nat}
    (endian : TargetEndian) (l : ByteSubLens) (cSrc : FixedByteCodec α n)
    (hPos : 0 < pad) (hTotPos : 0 < n + pad) (mem mem' : MemoryState) (v : α)
    (hPut :
      typedSubLensPut l (FixedByteCodec.padRight cSrc pad) mem v = some mem') :
    typedSubLensGet l (uintBvCodec endian (n + pad) hTotPos) mem' = none :=
  typedSubLens_padRight_init_decode_none l cSrc
    (uintBvCodec endian (n + pad) hTotPos) hPos
    (initDecoded_uintBvCodec endian (n + pad) hTotPos) mem mem' v hPut

private theorem initDecoded_cast {β : Type} {n1 n2 : Nat} (h : n1 = n2)
    {c : FixedByteCodec β n1} (hInit : InitDecodedCodec c) :
    InitDecodedCodec (h ▸ c) := by
  subst h
  exact hInit

theorem typedSubLens_padRight_array_none {α β : Type} {n pad m k : Nat}
    (l : ByteSubLens) (cSrc : FixedByteCodec α n)
    (cElem : FixedByteCodec β m) (hPos : 0 < pad)
    (hWidth : n + pad = k * m) (hInitElem : InitDecodedCodec cElem)
    (mem mem' : MemoryState) (v : α)
    (hPut :
      typedSubLensPut l (FixedByteCodec.padRight cSrc pad) mem v = some mem') :
    typedSubLensGet l (hWidth ▸ FixedByteCodec.array k cElem) mem' = none :=
  typedSubLens_padRight_init_decode_none l cSrc
    (hWidth ▸ FixedByteCodec.array k cElem) hPos
    (initDecoded_cast hWidth.symm (initDecoded_array hInitElem k))
    mem mem' v hPut

/-! ## 2. Part B: `FixedByteCodec` ↔ `PureLift.SpatialPin` Bridge -/

/-- Map an `AllocByte` to a `PureLift.CellVal`: `.init b _` → `.rawByte b` and
`.uninit` → `.uninit`. -/
@[expose] def allocByteToCell {Val : Type} : AllocByte → CellVal Val
  | .init b _ => .rawByte b
  | .uninit => .uninit

/-- Total computable `AllocByte` → `CellVal Val` conversion via `List.foldr`
(`0` `._unsafe_rec`). -/
@[expose] def allocBytesToCells {Val : Type} (bs : List AllocByte) : List (CellVal Val) :=
  bs.foldr (fun b acc => allocByteToCell b :: acc) []

/-- Inverse projection `CellVal Val` → `Option AllocByte` rejecting `.init`
cells. -/
@[expose] def cellToAllocByte {Val : Type} : CellVal Val → Option AllocByte
  | .rawByte b => some (.init b none)
  | .uninit => some .uninit
  | .init _ => none

/-- Total computable `CellVal Val` → `Option (List AllocByte)` via `List.foldr`
(`0` `._unsafe_rec`). -/
@[expose] def cellsToAllocBytes {Val : Type} (cells : List (CellVal Val)) :
    Option (List AllocByte) :=
  cells.foldr
    (fun c acc =>
      match cellToAllocByte c, acc with
      | some b, some tl => some (b :: tl)
      | _, _ => none)
    (some [])

theorem allocBytesToCells_length {Val : Type} (bs : List AllocByte) :
    (allocBytesToCells (Val := Val) bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons _ _ ih =>
    change (allocBytesToCells _).length + 1 = _ + 1
    exact congrArg Nat.succ ih

theorem cellsToAllocBytes_length {Val : Type} :
    ∀ {cells : List (CellVal Val)} {bs : List AllocByte},
      cellsToAllocBytes cells = some bs → bs.length = cells.length
  | [], [], _ => rfl
  | [], _ :: _, h => by nomatch h
  | c :: rest, bs, h => by
    dsimp only [cellsToAllocBytes] at h
    cases hc : cellToAllocByte c with
    | none =>
      change (match cellToAllocByte c, cellsToAllocBytes rest with
        | some b, some tl => some (b :: tl) | _, _ => none) = some bs at h
      rw [hc] at h
      nomatch h
    | some hd =>
      change (match cellToAllocByte c, cellsToAllocBytes rest with
        | some b, some tl => some (b :: tl) | _, _ => none) = some bs at h
      rw [hc] at h
      cases htl : cellsToAllocBytes rest with
      | none => rw [htl] at h; nomatch h
      | some tl =>
        rw [htl] at h
        injection h with hEq
        subst hEq
        rw [List.length_cons, List.length_cons, cellsToAllocBytes_length htl]

theorem cellsToAllocBytes_allocBytesToCells_of_noProv {Val : Type}
    (bs : List AllocByte) (hNoProv : NoProvBytes bs) :
    cellsToAllocBytes (allocBytesToCells (Val := Val) bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | uninit =>
      change (match some AllocByte.uninit,
          cellsToAllocBytes (allocBytesToCells tl) with
        | some b, some r => some (b :: r) | _, _ => none) = some (.uninit :: tl)
      rw [ih hNoProv]
    | init b prov =>
      have hSplit := noProvBytes_cons_head_none hNoProv
      rw [hSplit.1]
      change (match some (AllocByte.init b none),
          cellsToAllocBytes (allocBytesToCells tl) with
        | some b, some r => some (b :: r) | _, _ => none) =
        some (.init b none :: tl)
      rw [ih hSplit.2]

theorem hasUninitCell_allocBytesToCells {Val : Type} (bs : List AllocByte) :
    hasUninitCell (allocBytesToCells (Val := Val) bs) = !allBytesInit bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | uninit => rfl
    | init b prov =>
      change hasUninitCell (allocBytesToCells tl) = !allBytesInit tl
      exact ih

theorem initCellVals_allocBytesToCells {Val : Type} (bs : List AllocByte) :
    initCellVals (allocBytesToCells (Val := Val) bs) = [] := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | uninit => exact ih
    | init _ _ => exact ih

theorem cellsAccountedByVal_allocBytesToCells {Val : Type}
    (alg : ValAlgebra Val) (loans : List (LoanEntry Val)) (srcVal : Val)
    (bs : List AllocByte) :
    cellsAccountedByVal alg loans srcVal (allocBytesToCells bs) = true := by
  unfold cellsAccountedByVal
  rw [initCellVals_allocBytesToCells]

@[expose] def cellValReplicateZeroRaw {Val : Type} (n : Nat) :
    List (CellVal Val) :=
  List.replicate n (CellVal.rawByte 0)

@[expose] def isZeroRawByteCells {Val : Type} (n : Nat)
    (cells : List (CellVal Val)) : Bool :=
  Nat.beq cells.length n &&
  cells.foldr
    (fun c ih =>
      match c with
      | .rawByte b => (b == 0) && ih
      | _ => false)
    true

private theorem isZeroRawByteCells_replicate {Val : Type} (n : Nat) :
    isZeroRawByteCells (Val := Val) n (cellValReplicateZeroRaw n) = true := by
  have hLen : (cellValReplicateZeroRaw (Val := Val) n).length = n :=
    length_replicate_eq (CellVal.rawByte 0) n
  have hTrueAnd : ∀ b : Bool, (true && b) = b := fun _ => rfl
  unfold isZeroRawByteCells
  rw [(br_nat_beq_iff _ _).mpr hLen, hTrueAnd]
  induction n with
  | zero => rfl
  | succ q ih =>
    dsimp only [cellValReplicateZeroRaw] at ih
    dsimp only [cellValReplicateZeroRaw]
    rw [List.replicate_succ, br_foldr_cons]
    dsimp only
    have hZ0 : ((0 : UInt8) == 0) = true := rfl
    rw [hZ0, ih (length_replicate_eq (CellVal.rawByte 0) q)]
    rfl

/-- Lift any provenance-free `FixedByteCodec α n` into a `PureLift.SpatialCodec
Val` (`0` `noncomputable`, `0` `._unsafe_rec`). Values in `α` encode to exact
`n`-cell raw/uninit windows (`allocBytesToCells (c.encode a)`); non-`α` values
encode at length `n + 1` (`.init v :: replicate n (.rawByte 0)`), preventing any
length-preserving spatial mutation on a frozen `n`-byte block from falling back
to `.init v`. -/
@[expose] def spatialCodecOfFixedByteCodec {Val α : Type} {n : Nat}
    (cid : Nat) (c : FixedByteCodec α n) (hNoProv : c.NoProvCodec)
    (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v) :
    SpatialCodec Val where
  codecId := cid
  encode v :=
    match ofVal v with
    | some a => allocBytesToCells (c.encode a)
    | none => .init v :: cellValReplicateZeroRaw n
  decode cells :=
    if Nat.beq cells.length n then
      match cellsToAllocBytes cells with
      | some bs => (c.decode bs).map toVal
      | none => none
    else if Nat.beq cells.length (n + 1) then
      match cells with
      | .init v :: rest =>
        match ofVal v with
        | none => if isZeroRawByteCells n rest then some v else none
        | some _ => none
      | _ => none
    else
      none
  decode_encode v := by
    cases hOf : ofVal v with
    | some a =>
      have hLen : (allocBytesToCells (Val := Val) (c.encode a)).length = n := by
        rw [allocBytesToCells_length, c.encode_length a]
      have hBeq :
          Nat.beq (allocBytesToCells (Val := Val) (c.encode a)).length n =
            true :=
        (br_nat_beq_iff _ _).mpr hLen
      dsimp only
      rw [br_if_bool_true hBeq,
          cellsToAllocBytes_allocBytesToCells_of_noProv (c.encode a)
            (hNoProv a)]
      dsimp only
      rw [c.decode_encode a]
      exact congrArg some (toVal_ofVal v a hOf)
    | none =>
      have hLen :
          (CellVal.init v :: cellValReplicateZeroRaw n).length = n + 1 := by
        rw [List.length_cons]
        exact congrArg Nat.succ (length_replicate_eq (CellVal.rawByte 0) n)
      have hNotN :
          Nat.beq (CellVal.init v :: cellValReplicateZeroRaw n).length n =
            false := by
        rw [hLen]
        cases hB : Nat.beq (n + 1) n with
        | false => rfl
        | true =>
          have hEq := br_nat_eq_of_beq hB
          have hLt : n < n := by
            have h0 : n < n + 1 := Nat.lt_succ_self n
            rw [hEq] at h0
            exact h0
          exact False.elim (Nat.lt_irrefl n hLt)
      have hBeqSucc :
          Nat.beq (CellVal.init v :: cellValReplicateZeroRaw n).length (n + 1) =
            true :=
        (br_nat_beq_iff _ _).mpr hLen
      dsimp only
      rw [br_if_bool_false hNotN, br_if_bool_true hBeqSucc]
      rw [hOf, isZeroRawByteCells_replicate n]
      rfl

theorem spatialCodecOfFixedByteCodec_lawful {Val α : Type} {n : Nat}
    (cid : Nat) (c : FixedByteCodec α n) (hNoProv : c.NoProvCodec)
    (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v) :
    LawfulCodec
      (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal) :=
  (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal
    toVal_ofVal).decode_encode

theorem spatialCodecOfFixedByteCodec_encode_ofVal {Val α : Type} {n : Nat}
    (cid : Nat) (c : FixedByteCodec α n) (hNoProv : c.NoProvCodec)
    (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v)
    {v : Val} {a : α} (hv : ofVal v = some a) :
    (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal
      toVal_ofVal).encode v = allocBytesToCells (c.encode a) := by
  dsimp only [spatialCodecOfFixedByteCodec]
  rw [hv]

theorem spatialCodecOfFixedByteCodec_hasUninitCell_false {Val α : Type}
    {n : Nat} (cid : Nat) (c : FixedByteCodec α n)
    (hNoProv : c.NoProvCodec) (hInit : c.IsInitCodec)
    (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v)
    {v : Val} {a : α} (hv : ofVal v = some a) :
    hasUninitCell
      ((spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal
        toVal_ofVal).encode v) = false := by
  rw [spatialCodecOfFixedByteCodec_encode_ofVal cid c hNoProv toVal ofVal
      toVal_ofVal hv,
      hasUninitCell_allocBytesToCells]
  have hTrue : allBytesInit (c.encode a) = true := hInit a
  rw [hTrue]
  rfl

theorem spatialCodecOfFixedByteCodec_hasUninitCell_true_padRight
    {Val α : Type} {n pad : Nat} (cid : Nat) (c0 : FixedByteCodec α n)
    (hNoProv : (FixedByteCodec.padRight c0 pad).NoProvCodec)
    (hPos : 0 < pad) (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v)
    (a : α) (hRound : ofVal (toVal a) = some a) :
    hasUninitCell
      ((spatialCodecOfFixedByteCodec cid (FixedByteCodec.padRight c0 pad)
        hNoProv toVal ofVal toVal_ofVal).encode (toVal a)) = true := by
  rw [spatialCodecOfFixedByteCodec_encode_ofVal cid
      (FixedByteCodec.padRight c0 pad) hNoProv toVal ofVal toVal_ofVal hRound,
      hasUninitCell_allocBytesToCells,
      FixedByteCodec.allBytesInit_padRight_encode_eq_false c0 hPos a]
  rfl

private theorem findLoan_updateLoan_self {Val : Type} (lid : LoanId)
    (f : LoanEntry Val → LoanEntry Val)
    (hId : ∀ x, (f x).id = x.id) :
    ∀ (loans : List (LoanEntry Val)) (e : LoanEntry Val),
      findLoan lid loans = some e →
      findLoan lid (updateLoan lid f loans) = some (f e)
  | [], _, h => by nomatch h
  | x :: xs, e, h => by
    unfold updateLoan
    rw [br_foldr_cons]
    cases hEq : (x.id == lid) with
    | true =>
      change (if (x.id == lid) then some x else findLoan lid xs) = some e at h
      rw [br_if_bool_true hEq] at h
      injection h with hx
      subst hx
      rw [br_if_bool_true rfl]
      unfold findLoan
      rw [br_foldr_cons]
      rw [hId x, br_if_bool_true hEq]
    | false =>
      change (if (x.id == lid) then some x else findLoan lid xs) = some e at h
      rw [br_if_bool_false hEq] at h
      rw [br_if_bool_false rfl]
      unfold findLoan
      rw [br_foldr_cons]
      rw [br_if_bool_false hEq]
      exact findLoan_updateLoan_self lid f hId xs e h

private theorem countLoanId_updateLoan_self {Val : Type} (lid : LoanId)
    (f : LoanEntry Val → LoanEntry Val) (hId : ∀ x, (f x).id = x.id) :
    ∀ loans : List (LoanEntry Val),
      countLoanId lid (updateLoan lid f loans) = countLoanId lid loans
  | [] => rfl
  | x :: xs => by
    unfold updateLoan
    rw [br_foldr_cons]
    cases hEq : (x.id == lid) with
    | true =>
      rw [br_if_bool_true rfl]
      unfold countLoanId
      rw [br_foldr_cons, br_foldr_cons]
      change (if ((f x).id == lid) = true then
          countLoanId lid (updateLoan lid f xs) + 1
        else countLoanId lid (updateLoan lid f xs)) =
        (if (x.id == lid) = true then countLoanId lid xs + 1 else
          countLoanId lid xs)
      rw [hId x, br_if_bool_true hEq, br_if_bool_true hEq,
          countLoanId_updateLoan_self lid f hId xs]
    | false =>
      rw [br_if_bool_false rfl]
      unfold countLoanId
      rw [br_foldr_cons, br_foldr_cons]
      change (if (x.id == lid) = true then
          countLoanId lid (updateLoan lid f xs) + 1
        else countLoanId lid (updateLoan lid f xs)) =
        (if (x.id == lid) = true then countLoanId lid xs + 1 else
          countLoanId lid xs)
      rw [br_if_bool_false hEq, br_if_bool_false hEq,
          countLoanId_updateLoan_self lid f hId xs]

private theorem countSpatialBlockId_cons_zero {Val : Type} (bid : BlockId)
    (b : SpatialBlock Val) (rest : List (SpatialBlock Val))
    (hZero : countSpatialBlockId bid (b :: rest) = 0) :
    (b.blockId == bid) = false ∧ countSpatialBlockId bid rest = 0 := by
  dsimp only [countSpatialBlockId] at hZero
  cases hEq : (b.blockId == bid) with
  | true =>
    change (if (b.blockId == bid) then countSpatialBlockId bid rest + 1
      else countSpatialBlockId bid rest) = 0 at hZero
    rw [br_if_bool_true hEq] at hZero
    nomatch hZero
  | false =>
    change (if (b.blockId == bid) then countSpatialBlockId bid rest + 1
      else countSpatialBlockId bid rest) = 0 at hZero
    rw [br_if_bool_false hEq] at hZero
    exact ⟨rfl, hZero⟩

private theorem findSpatialBlock_append_singleton {Val : Type}
    (sp : List (SpatialBlock Val)) (blk : SpatialBlock Val)
    (hNotIn : hasSpatialBlockId blk.blockId sp = false) :
    findSpatialBlock (sp ++ [blk]) blk.blockId = some (blk, sp) := by
  have hCountZero : countSpatialBlockId blk.blockId sp = 0 := by
    dsimp only [hasSpatialBlockId] at hNotIn
    cases hc : countSpatialBlockId blk.blockId sp with
    | zero => rfl
    | succ _ =>
      change (countSpatialBlockId blk.blockId sp != 0) = false at hNotIn
      rw [hc] at hNotIn
      nomatch hNotIn
  have hFold :
      ∀ xs : List (SpatialBlock Val),
        countSpatialBlockId blk.blockId xs = 0 →
        (xs ++ [blk]).foldr
          (fun b
               (acc :
                 Bool × Option (SpatialBlock Val) × List (SpatialBlock Val)) =>
            match acc with
            | (dup, foundOpt, rest) =>
              if b.blockId == blk.blockId then
                match foundOpt with
                | some _ => (true, foundOpt, rest)
                | none => (dup, some b, rest)
              else
                (dup, foundOpt, b :: rest))
          (false, none, []) = (false, some blk, xs) := by
    intro xs hZ
    induction xs with
    | nil =>
      have hSelf : (blk.blockId == blk.blockId) = true :=
        beq_self_eq_true blk.blockId
      change (if (blk.blockId == blk.blockId) = true then (false, some blk, [])
        else (false, none, [blk])) = (false, some blk, [])
      rw [br_if_bool_true hSelf]
    | cons hd tl ih =>
      have hStep := countSpatialBlockId_cons_zero blk.blockId hd tl hZ
      rw [List.cons_append, br_foldr_cons]
      rw [ih hStep.2]
      dsimp only
      rw [br_if_bool_false hStep.1]
  unfold findSpatialBlock
  change
    (match
      (sp ++ [blk]).foldr
        (fun b
             (acc :
               Bool × Option (SpatialBlock Val) × List (SpatialBlock Val)) =>
          match acc with
          | (dup, foundOpt, rest) =>
            if b.blockId == blk.blockId then
              match foundOpt with
              | some _ => (true, foundOpt, rest)
              | none => (dup, some b, rest)
            else
              (dup, foundOpt, b :: rest))
        (false, none, []) with
     | (false, some found, updated) => some (found, updated)
     | _ => none) = some (blk, sp)
  rw [hFold sp hCountZero]

/-- Fail-closed freeze rejection: when `c.encode a` contains any `.uninit`
byte (`allBytesInit (c.encode a) = false`, such as `padRight c0 pad` with `0 <
pad`), `freezeToSpatialInState` fails closed `.fail`. -/
theorem spatialCodecOfFixedByteCodec_freeze_fails_of_uninit
    {Val α : Type} {n : Nat} (alg : ValAlgebra Val) (lid : LoanId)
    (cid : Nat) (c : FixedByteCodec α n) (hNoProv : c.NoProvCodec)
    (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v)
    (st : SymState Val) (e : LoanEntry Val) (a : α)
    (hFind : findLoan lid st.loans = some e)
    (hOf : ofVal e.cell.val = some a)
    (hUninit : allBytesInit (c.encode a) = false) :
    freezeToSpatialInState alg lid
      (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal)
      st = .fail := by
  let sc := spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal
  have hHasUninit : hasUninitCell (sc.encode e.cell.val) = true := by
    dsimp only [sc]
    rw [spatialCodecOfFixedByteCodec_encode_ofVal cid c hNoProv toVal ofVal
        toVal_ofVal hOf,
        hasUninitCell_allocBytesToCells, hUninit]
    rfl
  unfold freezeToSpatialInState
  cases hUniq : hasUniqueLoanId lid st.loans with
  | false => rfl
  | true =>
    dsimp only
    rw [hFind]
    dsimp only
    cases (!e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
        !noActiveChildLoanEdgesIn alg lid st.loans ||
        !noActiveChildRegionEdges lid st.regionGroups) with
    | true => rfl
    | false =>
      rw [hHasUninit]
      rfl

/-- Freeze + immediate reabsorption theorem for `spatialCodecOfFixedByteCodec`:
whenever loan `lid` is an unborrowed active mutable loan holding `v` (`ofVal v =
some a`), `c.IsInitCodec`, and `replaceableVal` holds reflexively for `v`,
`freezeToSpatialInState` succeeds (`= .ok stPinned`) and immediately calling
`reabsorbFromSpatialInState` succeeds (`= .ok stEnd`) leaving `stEnd.spatial =
st.spatial`, restoring `lid` to `.activeMut` with the exact same `e.cell`. -/
theorem spatialCodecOfFixedByteCodec_freeze_reabsorb
    {Val α : Type} {n : Nat} (alg : ValAlgebra Val) (lid : LoanId)
    (cid : Nat) (c : FixedByteCodec α n) (hNoProv : c.NoProvCodec)
    (hInit : c.IsInitCodec) (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v)
    (st : SymState Val) (e : LoanEntry Val) (a : α)
    (hUniq : hasUniqueLoanId lid st.loans = true)
    (hFind : findLoan lid st.loans = some e)
    (hMut : e.phase.isActiveMut = true)
    (hUnb : isUnborrowed e.cell.perm = true)
    (hNoChildLoan : noActiveChildLoanEdgesIn alg lid st.loans = true)
    (hNoChildRg : noActiveChildRegionEdges lid st.regionGroups = true)
    (hNoBid : hasSpatialBlockId st.nextSpatialTag st.spatial = false)
    (hNoLoanBlk : countBlocksForLoan lid st.spatial = 0)
    (hOf : ofVal e.cell.val = some a)
    (hRepl :
      replaceableVal alg
        (updateLoan lid
          (fun x => ⟨x.id,
            .spatialPinned st.nextSpatialTag
              (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal
                toVal_ofVal),
            x.cell, x.target⟩)
          st.loans)
        e.cell.val e.cell.val = true) :
    let sc := spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal
    let loans' := updateLoan lid
      (fun x => ⟨x.id, .spatialPinned st.nextSpatialTag sc, x.cell, x.target⟩)
      st.loans
    let blk : SpatialBlock Val :=
      ⟨st.nextSpatialTag, lid, .readWrite, st.nextSpatialTag, 0,
        allocBytesToCells (c.encode a)⟩
    let stPinned : SymState Val :=
      ⟨st.locals, loans', st.regionGroups, st.regionDeposits,
        st.spatial ++ [blk], st.nextSpatialTag + 1⟩
    let loansBack := updateLoan lid
      (fun x => ⟨x.id, .activeMut, ⟨e.cell.val, x.cell.perm⟩, x.target⟩)
      loans'
    let stEnd : SymState Val :=
      ⟨st.locals, loansBack, st.regionGroups, st.regionDeposits,
        st.spatial, st.nextSpatialTag + 1⟩
    freezeToSpatialInState alg lid sc st = .ok stPinned ∧
    reabsorbFromSpatialInState alg lid sc stPinned = .ok stEnd := by
  intro sc loans' blk stPinned loansBack stEnd
  have hEnc : sc.encode e.cell.val = allocBytesToCells (c.encode a) :=
    spatialCodecOfFixedByteCodec_encode_ofVal cid c hNoProv toVal ofVal
      toVal_ofVal hOf
  have hNoUninit : hasUninitCell (sc.encode e.cell.val) = false :=
    spatialCodecOfFixedByteCodec_hasUninitCell_false cid c hNoProv hInit toVal
      ofVal toVal_ofVal hOf
  have hAcc :
      cellsAccountedByVal alg st.loans e.cell.val (sc.encode e.cell.val) =
        true := by
    rw [hEnc]
    exact cellsAccountedByVal_allocBytesToCells alg st.loans e.cell.val
      (c.encode a)
  have hFreezeGuards :
      (!e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
        !noActiveChildLoanEdgesIn alg lid st.loans ||
        !noActiveChildRegionEdges lid st.regionGroups) = false := by
    rw [hMut, hUnb, hNoChildLoan, hNoChildRg]; rfl
  have hSpGuards :
      (hasSpatialBlockId st.nextSpatialTag st.spatial ||
        countBlocksForLoan lid st.spatial != 0) = false := by
    rw [hNoBid, hNoLoanBlk]; rfl
  have hFreeze : freezeToSpatialInState alg lid sc st = .ok stPinned := by
    unfold freezeToSpatialInState
    rw [hUniq]
    dsimp only
    rw [hFind]
    dsimp only
    rw [hFreezeGuards]
    rw [hEnc]
    rw [hEnc] at hNoUninit hAcc
    rw [hNoUninit, hAcc]
    rw [hSpGuards]
    rfl
  have hUniq' : hasUniqueLoanId lid loans' = true := by
    dsimp only [hasUniqueLoanId, loans']
    rw [countLoanId_updateLoan_self lid
        (fun x => ⟨x.id, .spatialPinned st.nextSpatialTag sc, x.cell, x.target⟩)
        (fun _ => rfl) st.loans]
    exact hUniq
  have hFind' :
      findLoan lid loans' =
        some ⟨e.id, .spatialPinned st.nextSpatialTag sc, e.cell, e.target⟩ :=
    findLoan_updateLoan_self lid
      (fun x => ⟨x.id, .spatialPinned st.nextSpatialTag sc, x.cell, x.target⟩)
      (fun _ => rfl) st.loans e hFind
  have hFindBlk : findSpatialBlock (st.spatial ++ [blk]) st.nextSpatialTag =
      some (blk, st.spatial) :=
    findSpatialBlock_append_singleton st.spatial blk hNoBid
  have hReabsorb : reabsorbFromSpatialInState alg lid sc stPinned = .ok stEnd := by
    unfold reabsorbFromSpatialInState
    change
      (if !hasUniqueLoanId lid loans' then EvalOutcome.fail
       else match findLoan lid loans' with
         | none => EvalOutcome.fail
         | some e' =>
           match e'.phase with
           | .spatialPinned bid pinnedCodec =>
             if pinnedCodec.codecId != sc.codecId then EvalOutcome.fail
             else match findSpatialBlock (st.spatial ++ [blk]) bid with
               | none => EvalOutcome.fail
               | some (b', restSpatial) =>
                 let writable := match b'.perm with | .readWrite => true | .readOnly => false
                 if b'.originLoan == lid && b'.provenanceTag == bid && writable &&
                    countBlocksForLoan lid restSpatial == 0 &&
                    b'.activeSubSplits == 0 && !hasUninitCell b'.cells &&
                    cellsAccountedByVal alg loans' e'.cell.val b'.cells then
                   match pinnedCodec.decode b'.cells with
                   | none => EvalOutcome.fail
                   | some v' =>
                     if !replaceableVal alg loans' e'.cell.val v' then
                       EvalOutcome.fail
                     else
                       let loans'' := updateLoan lid
                         (fun x => ⟨x.id, .activeMut, ⟨v', x.cell.perm⟩, x.target⟩)
                         loans'
                       EvalOutcome.ok ⟨st.locals, loans'', st.regionGroups,
                         st.regionDeposits, restSpatial, st.nextSpatialTag + 1⟩
                 else EvalOutcome.fail
           | _ => EvalOutcome.fail) = EvalOutcome.ok stEnd
    have hNotTrue : (!true) = false := rfl
    rw [hUniq', br_if_bool_false hNotTrue, hFind']
    dsimp only
    rw [br_nat_bne_self sc.codecId, br_if_bool_false rfl, hFindBlk]
    dsimp only
    have hUninitBlk : hasUninitCell blk.cells = false := by
      dsimp only [blk]
      rw [← hEnc]
      exact hNoUninit
    have hAccBlk : cellsAccountedByVal alg loans' e.cell.val blk.cells = true :=
      cellsAccountedByVal_allocBytesToCells alg loans' e.cell.val (c.encode a)
    have hL1 : (blk.originLoan == lid) = true := beq_self_eq_true lid
    have hL2 : (blk.provenanceTag == st.nextSpatialTag) = true :=
      beq_self_eq_true st.nextSpatialTag
    have hP :
        (match blk.perm with | .readWrite => true | .readOnly => false) =
          true := rfl
    have hZ0 : ((0 : Nat) == 0) = true := rfl
    rw [hL1, hL2, hP, hNoLoanBlk, hZ0, hUninitBlk, hAccBlk]
    have hCondTrue :
        (true && true && true && true && true && !false && true) = true := rfl
    rw [br_if_bool_true hCondTrue]
    dsimp only [blk]
    rw [← hEnc, sc.decode_encode e.cell.val]
    dsimp only
    rw [hRepl, br_if_bool_false hNotTrue]
  exact ⟨hFreeze, hReabsorb⟩

/-- Fail-closed reabsorption rejection on `.uninit`: if the spatial block for
pinned loan `lid` contains any `.uninit` cell (`hasUninitCell blk.cells =
true`), `reabsorbFromSpatialInState` fails closed `.fail` even if the codec
itself (`padUninit` / `padRight`) would have decoded `.uninit`. -/
theorem spatialCodecOfFixedByteCodec_reabsorb_fails_of_uninit_cell
    {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (sc : SpatialCodec Val) (st : SymState Val) (e : LoanEntry Val)
    (bid : BlockId) (pinnedCodec : SpatialCodec Val)
    (blk : SpatialBlock Val) (restSpatial : List (SpatialBlock Val))
    (hFind : findLoan lid st.loans = some e)
    (hPhase : e.phase = .spatialPinned bid pinnedCodec)
    (hBlk : findSpatialBlock st.spatial bid = some (blk, restSpatial))
    (hHasUninit : hasUninitCell blk.cells = true) :
    reabsorbFromSpatialInState alg lid sc st = .fail := by
  unfold reabsorbFromSpatialInState
  cases hasUniqueLoanId lid st.loans with
  | false => rfl
  | true =>
    dsimp only
    rw [hFind]
    dsimp only
    rw [hPhase]
    dsimp only
    cases pinnedCodec.codecId != sc.codecId with
    | true => rfl
    | false =>
      rw [hBlk]
      dsimp only
      rw [hHasUninit, br_and_not_true, br_false_and]
      rfl

/-- Fail-closed reabsorption rejection on invalid `n`-byte cells: if the
spatial block for pinned loan `lid` uses `spatialCodecOfFixedByteCodec`, has
exact width `blk.cells.length = n`, and `(cellsToAllocBytes blk.cells).bind
c.decode = none` (e.g., invalid enum/bool/niche byte or smuggled `.init` cell),
`reabsorbFromSpatialInState` fails closed `.fail`. -/
theorem spatialCodecOfFixedByteCodec_reabsorb_fails_of_bad_bytes
    {Val α : Type} {n : Nat} (alg : ValAlgebra Val) (lid : LoanId)
    (cid : Nat) (c : FixedByteCodec α n) (hNoProv : c.NoProvCodec)
    (toVal : α → Val) (ofVal : Val → Option α)
    (toVal_ofVal : ∀ (v : Val) (a : α), ofVal v = some a → toVal a = v)
    (st : SymState Val) (e : LoanEntry Val) (bid : BlockId)
    (blk : SpatialBlock Val) (restSpatial : List (SpatialBlock Val))
    (hFind : findLoan lid st.loans = some e)
    (hPhase :
      e.phase = .spatialPinned bid
        (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal))
    (hBlk : findSpatialBlock st.spatial bid = some (blk, restSpatial))
    (hLen : blk.cells.length = n)
    (hBad : (cellsToAllocBytes blk.cells).bind c.decode = none) :
    reabsorbFromSpatialInState alg lid
      (spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal)
      st = .fail := by
  let sc := spatialCodecOfFixedByteCodec cid c hNoProv toVal ofVal toVal_ofVal
  have hDecNone : sc.decode blk.cells = none := by
    dsimp only [sc, spatialCodecOfFixedByteCodec]
    rw [br_if_bool_true ((br_nat_beq_iff _ _).mpr hLen)]
    cases hRaw : cellsToAllocBytes blk.cells with
    | none => rfl
    | some bs =>
      rw [hRaw] at hBad
      dsimp only [Option.bind] at hBad
      dsimp only
      rw [hBad]
      rfl
  unfold reabsorbFromSpatialInState
  cases hasUniqueLoanId lid st.loans with
  | false => rfl
  | true =>
    dsimp only
    have hOuter : (!true) = false := rfl
    rw [br_if_bool_false hOuter]
    rw [hFind]
    dsimp only
    rw [hPhase]
    dsimp only
    have hCodecIdEq : (sc.codecId != sc.codecId) = false :=
      br_nat_bne_self sc.codecId
    rw [br_if_bool_false hCodecIdEq]
    rw [hBlk]
    dsimp only
    have hIfMatch :
        ∀ (cond : Bool) (x : Option Val) (f : Val → EvalOutcome (SymState Val)),
          x = none →
          (if cond = true then
            (match x with | none => EvalOutcome.fail | some v => f v)
           else EvalOutcome.fail) = EvalOutcome.fail := by
      intro cond x f hx
      cases cond with
      | false => rfl
      | true => rw [hx]; rfl
    exact hIfMatch _ _ _ hDecNone

end Anneal.PureLift

end
