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
public import Init.SimpLemmas
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.Data.Fin.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.InitLemmas
public import Anneal.NatBitwise
public import Anneal.BitVec
public import Anneal.BitVecArith
public import Anneal.LeBytes
public import Anneal.ListChunks
public import Anneal.MirWp
public import Anneal.Core.BitValidity

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.InitLemmas Anneal.MirWp

/-!
# BitVec, BitVecArith, and LeBytes to MIR Scalar Bridge

Connects the pure 3-axiom, foundation-locked algebraic libraries
(`Anneal.BitVec`, `Anneal.BitVecArith`, `Anneal.LeBytes`, and
`Anneal.ListChunks`) directly to the operational MIR semantics
(`Trusted.MirSemantics.Ops`, `Trusted.MirSemantics.Bytes`) and
`Anneal.MirWp.Scalars`:

1. **Width Alignment & Constant Power Helpers (`8 * sz` vs `sz * 8`,
   `IntWidth`):** Zero-cost `toLeWidth` / `ofLeWidth` re-indexing,
   `intWidthModulus` power identities, and `bvToScalar` / `scalarToBv`
   round-trip embeddings between `ScalarVal` and width-indexed
   `BitVec (8 * w.byteSize)`.
2. **Two's-Complement Value & Ordering Bridges (`decodeScalar`, `signExtend`,
   `slt`, `sle`):** Exact signed/unsigned `decodeScalar`, `bvToInt`, and
   `bvOfInt` normalizations via `Anneal.InitLemmas.IntBalance`, proving
   `<` / `≤` agreement with `Anneal.BitVecArith.slt` and
   `Anneal.BitVecArith.sle`.
3. **Operational `evalBinOp`, `evalUnOp`, and `evalIntToIntCast` Bridges:**
   Soundness equations linking MIR `.bitAnd`/`.bitOr`/`.bitXor`, `.add`/`.sub`/
   `.mul` (both signed and unsigned wrapping, plus unsigned `.addWithOverflow` /
   `.subWithOverflow` / `.addUnchecked` / `.subUnchecked`), unsigned `.div`/
   `.rem` (`Anneal.BitVec.udiv` / `Anneal.BitVecArith.urem`), `.shl`/`.shr`/
   `.shlUnchecked`/`.shrUnchecked` (`shl` / `ushr` / `ashr`), signed/unsigned
   comparisons, unary `.not`/`.neg`, and `CastKind.IntToInt` (`setWidth` /
   `signExtend`) directly to `Anneal.BitVec` and `Anneal.BitVecArith`.
4. **Byte-Order Serialization & Chunking Adequacy (`Bytes` <-> `LeBytes` /
   `ListChunks`):** Exact agreement and round-trips between `leBytesOfNat`,
   `natOfLeBytes`, `encodeUInt`, `decodeUInt`, `initBytes?`, `encodeVal`, and
   `decodeVal` across both `.little` and `.big` `TargetEndian` (including
   `profileTargetEndian`), paired with `chunksOf` extraction commutativity.
-/

/-! ## 0. Width Alignment & Modular Arithmetic Helpers -/

/-- `Nat.mul sz 8` (byte-list bit width) equals `8 * sz`. -/
theorem natMul_eight (sz : Nat) : Nat.mul sz 8 = 8 * sz :=
  Nat.mul_comm sz 8

private theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_add_mod_right (x z : Nat) :
    Nat.mod (x + z) z = Nat.mod x z :=
  Nat.add_mod_right x z

private theorem nat_mod_self (n : Nat) : Nat.mod n n = 0 :=
  Nat.mod_self n

private theorem nat_zero_mod (n : Nat) : Nat.mod 0 n = 0 :=
  Nat.zero_mod n

private theorem nat_mod_zero (a : Nat) : Nat.mod a 0 = a :=
  Nat.mod_zero a

private theorem nat_mod_mod (a n : Nat) :
    Nat.mod (Nat.mod a n) n = Nat.mod a n := by
  cases n with
  | zero => rw [nat_mod_zero, nat_mod_zero]
  | succ k => exact nat_mod_eq_of_lt (Nat.mod_lt a (Nat.zero_lt_succ k))

private theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_lt_of_add_lt_add_right {a b c : Nat}
    (h : a + c < b + c) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge => exact False.elim (Nat.not_lt_of_ge (Nat.add_le_add_right hge c) h)

private theorem nat_lt_of_add_lt_add_left {a b c : Nat}
    (h : a + b < a + c) : b < c := by
  cases Nat.lt_or_ge b c with
  | inl hlt => exact hlt
  | inr hge => exact False.elim (Nat.not_lt_of_ge (Nat.add_le_add_left hge a) h)

private theorem if_bool_true {α : Type u} {b : Bool} (hb : b = true)
    [d : Decidable (b = true)] {t e : α} :
    (@ite α (b = true) d t e) = t := by
  cases d with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hb)

private theorem if_bool_false {α : Type u} {b : Bool} (hb : b = false)
    [d : Decidable (b = true)] {t e : α} :
    (@ite α (b = true) d t e) = e := by
  cases d with
  | isTrue h => rw [hb] at h; cases h
  | isFalse _ => rfl

private theorem if_true_eq {α : Type u} [d : Decidable (true = true)]
    {a b : α} : (@ite α (true = true) d a b) = a :=
  if_bool_true rfl

private theorem if_false_eq {α : Type u} [d : Decidable (false = true)]
    {a b : α} : (@ite α (false = true) d a b) = b :=
  if_bool_false rfl

private theorem bitVec_toNat_lt_pow {w : Nat} (x : BitVec w) :
    x.toNat < Nat.pow 2 w := x.isLt

private theorem int_ofNat_sub_ofNat (a b : Nat) :
    Int.ofNat a - Int.ofNat b = Int.subNatNat a b := by
  cases b with
  | zero =>
    change Int.ofNat a = Int.subNatNat a 0
    unfold Int.subNatNat
    rw [Nat.zero_sub, Nat.sub_zero]
  | succ _ => rfl

private theorem int_ofNat_le_iff {a b : Nat} :
    Int.ofNat a ≤ Int.ofNat b ↔ a ≤ b := by
  change Int.NonNeg (Int.ofNat b - Int.ofNat a) ↔ a ≤ b
  rw [int_ofNat_sub_ofNat]
  constructor
  · intro h
    cases Nat.lt_or_ge b a with
    | inl hlt =>
      have hPos : 0 < a - b := Nat.zero_lt_sub_of_lt hlt
      cases hd : a - b with
      | zero =>
        rw [hd] at hPos
        nomatch hPos
      | succ k =>
        unfold Int.subNatNat at h
        rw [hd] at h
        nomatch h
    | inr hge => exact hge
  · intro h
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le h]
    exact Int.NonNeg.mk (b - a)

private theorem int_ofNat_lt_iff {a b : Nat} :
    Int.ofNat a < Int.ofNat b ↔ a < b := by
  change Int.ofNat (a + 1) ≤ Int.ofNat b ↔ a + 1 ≤ b
  exact int_ofNat_le_iff

private theorem int_negSucc_lt_ofNat (ma mb : Nat) :
    Int.negSucc ma < Int.ofNat mb := by
  cases ma with
  | zero => exact int_ofNat_le_iff.mpr (Nat.zero_le mb)
  | succ k => exact Int.NonNeg.mk (mb + (k + 1))

private theorem int_negSucc_lt_zero (m : Nat) :
    Int.negSucc m < 0 :=
  int_negSucc_lt_ofNat m 0

private theorem int_negSucc_le_negSucc_iff {a b : Nat} :
    Int.negSucc a ≤ Int.negSucc b ↔ b ≤ a := by
  change Int.NonNeg (Int.subNatNat (a + 1) (b + 1)) ↔ b ≤ a
  have hSub : Int.subNatNat (a + 1) (b + 1) = Int.subNatNat a b := by
    unfold Int.subNatNat
    rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
  rw [hSub, ← int_ofNat_sub_ofNat]
  exact int_ofNat_le_iff

private theorem int_negSucc_lt_negSucc_iff {a b : Nat} :
    Int.negSucc a < Int.negSucc b ↔ b < a := by
  cases a with
  | zero =>
    constructor
    · intro h
      have hF : Int.ofNat 0 ≤ Int.negSucc b := h
      cases hF
    · intro h
      nomatch h
  | succ a' =>
    have hL : (Int.negSucc (a' + 1) < Int.negSucc b) =
        (Int.negSucc a' ≤ Int.negSucc b) := rfl
    rw [hL, int_negSucc_le_negSucc_iff]
    exact ⟨fun h => Nat.succ_le_succ h, fun h => Nat.le_of_succ_le_succ h⟩

private theorem int_negSucc_le_ofNat (a b : Nat) :
    Int.negSucc a ≤ Int.ofNat b :=
  Int.NonNeg.mk (b + (a + 1))

private theorem int_not_ofNat_le_negSucc (a b : Nat) :
    ¬ (Int.ofNat a ≤ Int.negSucc b) := by
  cases a with
  | zero => exact fun h => nomatch h
  | succ k => exact fun h => nomatch h

private theorem int_le_refl (x : Int) : x ≤ x := by
  cases x with
  | ofNat n => exact int_ofNat_le_iff.mpr (Nat.le_refl n)
  | negSucc k => exact int_negSucc_le_negSucc_iff.mpr (Nat.le_refl k)

private theorem mod_mod_of_mul_right (n a b : Nat) :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDiv : Nat.mod n (a * b) + a * (b * Nat.div n (a * b)) = n := by
    rw [← Nat.mul_assoc]
    exact Nat.mod_add_div n (a * b)
  exact (nat_add_mul_mod_self_left (Nat.mod n (a * b)) a
    (b * Nat.div n (a * b))).symm.trans (congrArg (fun k => Nat.mod k a) hDiv)

private theorem mod_pow_of_le {m k n : Nat} (h : m ≤ k) :
    Nat.mod (Nat.mod n (Nat.pow 2 k)) (Nat.pow 2 m) =
      Nat.mod n (Nat.pow 2 m) := by
  have hk : Nat.pow 2 k = Nat.pow 2 m * Nat.pow 2 (k - m) := by
    have hEq : k = m + (k - m) := (Nat.add_sub_of_le h).symm
    have hP := congrArg (Nat.pow 2) hEq
    rw [nat_pow_add] at hP
    exact hP
  rw [hk]
  exact mod_mod_of_mul_right n (Nat.pow 2 m) (Nat.pow 2 (k - m))

private theorem mod_add_cancel_left (a b m : Nat) :
    Nat.mod (Nat.mod a m + b) m = Nat.mod (a + b) m := by
  have h : a + b = (Nat.mod a m + b) + m * Nat.div a m := by
    have ha := nat_div_add_mod a m
    rw [Nat.add_comm (m * Nat.div a m) (Nat.mod a m)] at ha
    have h1 := congrArg (fun z => z + b) ha
    rw [Nat.add_right_comm (Nat.mod a m) (m * Nat.div a m) b] at h1
    exact h1.symm
  rw [h, nat_add_mul_mod_self_left]

private theorem mod_add_cancel_right (a b m : Nat) :
    Nat.mod (a + Nat.mod b m) m = Nat.mod (a + b) m := by
  rw [Nat.add_comm a (Nat.mod b m), mod_add_cancel_left, Nat.add_comm]

private theorem mod_mul_cancel_left (a b m : Nat) :
    Nat.mod (Nat.mod a m * b) m = Nat.mod (a * b) m := by
  have h : a * b = Nat.mod a m * b + m * (Nat.div a m * b) := by
    have ha := nat_div_add_mod a m
    rw [Nat.add_comm (m * Nat.div a m) (Nat.mod a m)] at ha
    have h1 := congrArg (fun z => z * b) ha
    rw [Nat.add_mul, Nat.mul_assoc] at h1
    exact h1.symm
  rw [h, nat_add_mul_mod_self_left]

private theorem mod_mul_cancel_right (a b m : Nat) :
    Nat.mod (a * Nat.mod b m) m = Nat.mod (a * b) m := by
  rw [Nat.mul_comm a (Nat.mod b m), mod_mul_cancel_left, Nat.mul_comm]

private theorem nat_mod_cancel_add_right {a₁ a₂ b M : Nat} (hM : 0 < M)
    (h : Nat.mod (a₁ + b) M = Nat.mod (a₂ + b) M) :
    Nat.mod a₁ M = Nat.mod a₂ M := by
  let r := Nat.mod b M
  have hrLe : r ≤ M := Nat.le_of_lt (Nat.mod_lt b hM)
  have hCancel : ∀ x : Nat, Nat.mod (Nat.mod (x + b) M + (M - r)) M =
      Nat.mod x M := fun x => by
    rw [mod_add_cancel_left, Nat.add_assoc,
      ← mod_add_cancel_right x (b + (M - r)) M,
      ← mod_add_cancel_left b (M - r) M]
    change Nat.mod (x + Nat.mod (r + (M - r)) M) M = Nat.mod x M
    rw [Nat.add_comm r (M - r), Nat.sub_add_cancel hrLe, mod_add_cancel_right,
      nat_add_mod_right]
  have h1 := congrArg (fun z => Nat.mod (z + (M - r)) M) h
  rw [hCancel a₁, hCancel a₂] at h1
  exact h1

private theorem sub_add_comm_of_le {a b c : Nat} (h : b ≤ a) :
    a - b + c = a + c - b := by
  have h1 : (a - b + c) + b = a + c := by
    rw [Nat.add_right_comm, Nat.sub_add_cancel h]
  have h2 := congrArg (fun z => z - b) h1
  rw [Nat.add_sub_cancel] at h2
  exact h2

private theorem nat_sub_sub_cancel_of_le {a b : Nat} (h : a ≤ b) :
    b - (b - a) = a := by
  have h1 : (b - a) + a = b := Nat.sub_add_cancel h
  have h2 := congrArg (fun z => z - (b - a)) h1
  rw [Nat.add_comm (b - a) a, Nat.add_sub_cancel] at h2
  exact h2.symm

/-! ## 1. Width Alignment (`8 * sz` vs `sz * 8`) & `ScalarVal` Embeddings -/

/-- Re-index a scalar-width bitvector (`BitVec (8 * sz)`) at the byte-list
bit width (`BitVec (sz * 8)` used by `Anneal.LeBytes` and `IntWidth.bitWidth`).
-/
@[expose] def toLeWidth {sz : Nat} (x : BitVec (8 * sz)) : BitVec (sz * 8) :=
  BitVec.ofNatLT x.toNat
    (Nat.lt_of_lt_of_le x.isLt
      (Nat.le_of_eq (congrArg (Nat.pow 2) (Nat.mul_comm 8 sz))))

/-- Re-index a byte-list-width bitvector (`BitVec (sz * 8)`) at the scalar
bit width (`BitVec (8 * sz)`). -/
@[expose] def ofLeWidth {sz : Nat} (x : BitVec (sz * 8)) : BitVec (8 * sz) :=
  BitVec.ofNatLT x.toNat
    (Nat.lt_of_lt_of_le x.isLt
      (Nat.le_of_eq (congrArg (Nat.pow 2) (Nat.mul_comm sz 8))))

@[simp] theorem toNat_toLeWidth {sz : Nat} (x : BitVec (8 * sz)) :
    (toLeWidth x).toNat = x.toNat :=
  rfl

@[simp] theorem toNat_ofLeWidth {sz : Nat} (x : BitVec (sz * 8)) :
    (ofLeWidth x).toNat = x.toNat :=
  rfl

@[simp] theorem ofLeWidth_toLeWidth {sz : Nat} (x : BitVec (8 * sz)) :
    ofLeWidth (toLeWidth x) = x :=
  Anneal.BitVec.eq_of_toNat_eq rfl

@[simp] theorem toLeWidth_ofLeWidth {sz : Nat} (x : BitVec (sz * 8)) :
    toLeWidth (ofLeWidth x) = x :=
  Anneal.BitVec.eq_of_toNat_eq rfl

/-- `toLeWidth` is injective. -/
theorem toLeWidth_injective {sz : Nat} {x y : BitVec (8 * sz)}
    (h : toLeWidth x = toLeWidth y) : x = y := by
  rw [← ofLeWidth_toLeWidth x, ← ofLeWidth_toLeWidth y, h]

/-- `toLeWidth` commutes with `BitVec.ofNat`. -/
theorem toLeWidth_ofNat (sz a : Nat) :
    toLeWidth (BitVec.ofNat (8 * sz) a) = BitVec.ofNat (sz * 8) a := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_toLeWidth, Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_ofNat,
    Nat.mul_comm]

/-- `BitVec.ofNat w x.toNat` equals `x`. -/
theorem ofNat_toNat_self {w : Nat} (x : BitVec w) :
    BitVec.ofNat w x.toNat = x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

/-- `IntWidth.bitWidth` equals `8 * w.byteSize` (the `bitWidth`-on-the-left,
`8 * _` orientation of `Anneal.Core.intWidth_bitWidth_eq`). -/
theorem intWidth_bitWidth_eq_eight_mul (w : IntWidth) :
    w.bitWidth = 8 * w.byteSize :=
  (intWidth_bitWidth_eq w).symm.trans (Nat.mul_comm w.byteSize 8)

/-- `intWidthModulus w` is `Nat.pow 2 w.bitWidth`. -/
theorem intWidthModulus_eq_pow (w : IntWidth) :
    intWidthModulus w = Nat.pow 2 w.bitWidth := by
  cases w <;> rfl

/-- `intWidthModulus w` is `Nat.pow 2 (8 * w.byteSize)`. -/
theorem intWidthModulus_eq_pow_eight (w : IntWidth) :
    intWidthModulus w = Nat.pow 2 (8 * w.byteSize) := by
  rw [intWidthModulus_eq_pow, intWidth_bitWidth_eq_eight_mul]

/-- `intWidthModulus w ≤ 2 ^ 128` for every `IntWidth`. -/
private theorem intWidthModulus_le_pow128 (w : IntWidth) :
    intWidthModulus w ≤ Nat.pow 2 128 := by
  rw [intWidthModulus_eq_pow]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (intWidth_bitWidth_le_128 w)

/-- `Trusted.MirSemantics.bvAnd` agrees with `Anneal.BitVec.and` at 128 bits.
-/
theorem bvAnd_eq_and (x y : BitVec 128) :
    bvAnd x y = Anneal.BitVec.and x y := by
  apply Anneal.BitVec.eq_of_toNat_eq
  unfold bvAnd
  rw [Anneal.BitVec.toNat_ofNat, ← Anneal.BitVec.toNat_and]
  exact nat_mod_eq_of_lt (Anneal.BitVec.and x y).isLt

/-- `Trusted.MirSemantics.bvOr` agrees with `Anneal.BitVec.or` at 128 bits. -/
theorem bvOr_eq_or (x y : BitVec 128) :
    bvOr x y = Anneal.BitVec.or x y := by
  apply Anneal.BitVec.eq_of_toNat_eq
  unfold bvOr
  rw [Anneal.BitVec.toNat_ofNat, ← Anneal.BitVec.toNat_or]
  exact nat_mod_eq_of_lt (Anneal.BitVec.or x y).isLt

/-- `Trusted.MirSemantics.bvXor` agrees with `Anneal.BitVec.xor` at 128 bits.
-/
theorem bvXor_eq_xor (x y : BitVec 128) :
    bvXor x y = Anneal.BitVec.xor x y := by
  apply Anneal.BitVec.eq_of_toNat_eq
  unfold bvXor
  rw [Anneal.BitVec.toNat_ofNat, ← Anneal.BitVec.toNat_xor]
  exact nat_mod_eq_of_lt (Anneal.BitVec.xor x y).isLt

/-- Exact `.toNat` of zero-extending `x : BitVec w` to `v` bits when `w ≤ v`.
-/
theorem toNat_bvZeroExtend_of_le {w v : Nat} (h : w ≤ v) (x : BitVec w) :
    (bvZeroExtend v x).toNat = x.toNat := by
  unfold bvZeroExtend
  rw [Anneal.BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) h))

/-- Construct a well-formed `Trusted.MirModel.ScalarVal` at `(w, s)` directly
from a width-indexed `BitVec (8 * w.byteSize)`. -/
@[expose] noncomputable def bvToScalar (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) : ScalarVal :=
  ⟨w, s, bvZeroExtend 128 x⟩

private theorem bvToScalar_width (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) : (bvToScalar w s x).width = w := rfl

private theorem bvToScalar_signed (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) : (bvToScalar w s x).signed = s := rfl

/-- Project any `ScalarVal` into its canonical `BitVec (8 * sv.width.byteSize)`
bit pattern. -/
@[expose] noncomputable def scalarToBv (sv : ScalarVal) :
    BitVec (8 * sv.width.byteSize) :=
  BitVec.ofNat (8 * sv.width.byteSize) sv.bits.toNat

private theorem bvToScalar_bits_toNat (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    (bvToScalar w s x).bits.toNat = x.toNat := by
  unfold bvToScalar
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  exact toNat_bvZeroExtend_of_le hw x

/-- `bvZeroExtend 128 x` is fixed by `truncateBits w`. -/
theorem truncateBits_bvZeroExtend (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    truncateBits w (bvZeroExtend 128 x) = bvZeroExtend 128 x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  rw [toNat_truncateBits, toNat_bvZeroExtend_of_le hw x,
    intWidthModulus_eq_pow_eight]
  exact nat_mod_eq_of_lt x.isLt

/-- Every `bvToScalar w s x` passes `ScalarVal.wf`. -/
theorem bvToScalar_wf (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    (bvToScalar w s x).wf = true := by
  unfold ScalarVal.wf bvToScalar
  dsimp only
  rw [truncateBits_bvZeroExtend]
  exact beq_self_eq_true (bvZeroExtend 128 x)

/-- Every `bvToScalar w s x` passes `checkVal · (.int w s)`. -/
theorem checkVal_bvToScalar (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    checkVal (.scalar (bvToScalar w s x)) (.int w s) = true := by
  unfold checkVal Val.ty?
  dsimp only
  rw [bvToScalar_wf w s x, if_true_eq]
  cases w <;> cases s <;> rfl

/-- Left inverse: `scalarToBv` recovers `x` from `bvToScalar w s x`. -/
theorem scalarToBv_bvToScalar (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    scalarToBv (bvToScalar w s x) = x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  unfold scalarToBv
  rw [Anneal.BitVec.toNat_ofNat, bvToScalar_bits_toNat]
  exact nat_mod_eq_of_lt x.isLt

/-- Right inverse: any well-formed `ScalarVal` (`sv.wf = true`) equals
`bvToScalar sv.width sv.signed (scalarToBv sv)`. -/
theorem bvToScalar_scalarToBv_of_wf {sv : ScalarVal} (hwf : sv.wf = true) :
    bvToScalar sv.width sv.signed (scalarToBv sv) = sv := by
  have hTrunc : truncateBits sv.width sv.bits = sv.bits := by
    unfold ScalarVal.wf at hwf
    exact of_decide_eq_true hwf
  have hLt : sv.bits.toNat < Nat.pow 2 (8 * sv.width.byteSize) := by
    rw [← hTrunc, toNat_truncateBits, intWidthModulus_eq_pow_eight]
    exact Nat.mod_lt _ (nat_two_pow_pos _)
  cases sv with
  | mk width signed bits =>
    dsimp only [bvToScalar, scalarToBv]
    have hBv : bvZeroExtend 128
          (BitVec.ofNat (8 * width.byteSize) bits.toNat) = bits := by
      apply Anneal.BitVec.eq_of_toNat_eq
      have hw : 8 * width.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 width
      rw [toNat_bvZeroExtend_of_le hw, Anneal.BitVec.toNat_ofNat]
      exact nat_mod_eq_of_lt hLt
    rw [hBv]

/-- `bvToScalar w s` is injective. -/
theorem bvToScalar_injective {w : IntWidth} {s : Bool}
    {x y : BitVec (8 * w.byteSize)}
    (h : bvToScalar w s x = bvToScalar w s y) : x = y := by
  have hs : (bvToScalar w s x).bits = (bvToScalar w s y).bits :=
    congrArg ScalarVal.bits h
  have ht : x.toNat = y.toNat := by
    rw [← bvToScalar_bits_toNat w s x, ← bvToScalar_bits_toNat w s y, hs]
  exact Anneal.BitVec.eq_of_toNat_eq ht

/-! ## 2. Two's-Complement `bvOfInt`, `decodeScalar`, `slt`, and `sle` Bridges
-/

private theorem intEmod_ofNat_two_pow (n m : Nat) :
    intEmod (Int.ofNat m) (Int.ofNat (Nat.pow 2 n)) =
      Int.ofNat (Nat.mod m (Nat.pow 2 n)) := rfl

private theorem intEmod_negSucc_two_pow (n m : Nat) :
    intEmod (Int.negSucc m) (Int.ofNat (Nat.pow 2 n)) =
      Int.ofNat (Nat.pow 2 n - Nat.succ (Nat.mod m (Nat.pow 2 n))) := by
  unfold intEmod Int.natAbs Int.subNatNat
  dsimp only
  have hSub : Nat.succ (Nat.mod m (Nat.pow 2 n)) - Nat.pow 2 n = 0 :=
    Nat.sub_eq_zero_of_le (Nat.mod_lt m (nat_two_pow_pos n))
  rw [hSub]

/-- `.toNat` of `bvOfInt n (Int.ofNat m)`. -/
theorem toNat_bvOfInt_ofNat (n m : Nat) :
    (bvOfInt n (Int.ofNat m)).toNat = Nat.mod m (Nat.pow 2 n) := by
  unfold bvOfInt
  rw [intEmod_ofNat_two_pow, Anneal.BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.mod_lt m (nat_two_pow_pos n))

/-- `.toNat` of `bvOfInt n (Int.negSucc m)`. -/
theorem toNat_bvOfInt_negSucc (n m : Nat) :
    (bvOfInt n (Int.negSucc m)).toNat =
      Nat.pow 2 n - Nat.succ (Nat.mod m (Nat.pow 2 n)) := by
  unfold bvOfInt
  rw [intEmod_negSucc_two_pow, Anneal.BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt
    (Nat.sub_lt (nat_two_pow_pos n) (Nat.zero_lt_succ _))

private theorem mod_two_pow_sub_succ_mod {W N : Nat} (hW : W ≤ N) (m : Nat) :
    Nat.mod (Nat.pow 2 N - Nat.succ (Nat.mod m (Nat.pow 2 N)))
        (Nat.pow 2 W) =
      Nat.pow 2 W - 1 - Nat.mod m (Nat.pow 2 W) := by
  let P := Nat.pow 2 W
  have hPpos : 0 < P := nat_two_pow_pos W
  let K := Nat.pow 2 (N - W)
  have hKpos : 0 < K := nat_two_pow_pos (N - W)
  have hPN : Nat.pow 2 N = P * K := by
    have hEq : N = W + (N - W) := (Nat.add_sub_of_le hW).symm
    have hPow := congrArg (Nat.pow 2) hEq
    rw [nat_pow_add] at hPow
    exact hPow
  let r := Nat.mod m P
  let q := Nat.div (Nat.mod m (Nat.pow 2 N)) P
  have hrLt : r < P := Nat.mod_lt m hPpos
  have hModEq : Nat.mod (Nat.mod m (Nat.pow 2 N)) P = r := mod_pow_of_le hW
  have hDecomp : Nat.mod m (Nat.pow 2 N) = P * q + r := by
    have h1 := nat_div_add_mod (Nat.mod m (Nat.pow 2 N)) P
    rw [hModEq] at h1
    exact h1.symm
  have hqLt : q < K := by
    have h2 : P * q < P * K := by
      have h1 : P * q ≤ P * q + r := Nat.le_add_right (P * q) r
      rw [← hDecomp] at h1
      have hModLt : Nat.mod m (Nat.pow 2 N) < P * K := by
        rw [← hPN]
        exact Nat.mod_lt m (nat_two_pow_pos N)
      exact Nat.lt_of_le_of_lt h1 hModLt
    cases Nat.lt_or_ge q K with
    | inl hlt => exact hlt
    | inr hge =>
      exact False.elim (Nat.not_le_of_gt h2 (Nat.mul_le_mul_left P hge))
  have hK1 : 1 ≤ K := hKpos
  have hqK1 : q ≤ K - 1 := Nat.le_sub_one_of_lt hqLt
  have hSum : Nat.pow 2 N =
      (Nat.pow 2 W - 1 - r + P * (K - 1 - q)) +
        Nat.succ (Nat.mod m (Nat.pow 2 N)) := by
    have h1 : Nat.succ (Nat.mod m (Nat.pow 2 N)) = P * q + (r + 1) := by
      rw [hDecomp]
      rfl
    have hSubR : (P - 1 - r) + (r + 1) = P := by
      have hrLe : r ≤ P - 1 := Nat.le_sub_one_of_lt hrLt
      have hShift : P - 1 - r + (1 + r) = (P - 1 - r + r) + 1 := by
        rw [Nat.add_comm 1 r, ← Nat.add_assoc]
      rw [Nat.add_comm r 1, hShift, Nat.sub_add_cancel hrLe,
        Nat.sub_add_cancel hPpos]
    have hMulK : P + P * (K - 1 - q) + P * q = P * K := by
      have hK_eq : 1 + (K - 1 - q) + q = K := by
        rw [Nat.add_assoc 1 (K - 1 - q) q, Nat.sub_add_cancel hqK1,
          Nat.add_comm 1 (K - 1), Nat.sub_add_cancel hK1]
      have hMul1 := congrArg (fun z => P * z) hK_eq
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hMul1
      exact hMul1
    rw [h1, hPN]
    rw [Nat.add_assoc (P - 1 - r) (P * (K - 1 - q)) (P * q + (r + 1))]
    rw [← Nat.add_assoc (P * (K - 1 - q)) (P * q) (r + 1)]
    rw [Nat.add_comm (P * (K - 1 - q) + P * q) (r + 1)]
    rw [← Nat.add_assoc (P - 1 - r) (r + 1) (P * (K - 1 - q) + P * q)]
    rw [hSubR, ← Nat.add_assoc P (P * (K - 1 - q)) (P * q), hMulK]
  have hDiff : Nat.pow 2 N - Nat.succ (Nat.mod m (Nat.pow 2 N)) =
      (Nat.pow 2 W - 1 - r) + P * (K - 1 - q) := by
    have h2 := congrArg (fun z => z - Nat.succ (Nat.mod m (Nat.pow 2 N))) hSum
    rw [Nat.add_sub_cancel] at h2
    exact h2
  rw [hDiff, nat_add_mul_mod_self_left]
  exact nat_mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.sub_le (Nat.pow 2 W - 1) r)
      (Nat.sub_lt hPpos Nat.one_pos))

/-- Truncating `bvOfInt 128 (.ofNat m)` to `w` computes
`m % 2^(8 * w.byteSize)`. -/
theorem toNat_truncateBits_bvOfInt_ofNat (w : IntWidth) (m : Nat) :
    (truncateBits w (bvOfInt 128 (Int.ofNat m))).toNat =
      Nat.mod m (Nat.pow 2 (8 * w.byteSize)) := by
  rw [toNat_truncateBits, toNat_bvOfInt_ofNat, intWidthModulus_eq_pow_eight]
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  exact mod_pow_of_le hw

/-- Truncating `bvOfInt 128 (.negSucc m)` to `w` computes the bit complement
of `m % 2^(8 * w.byteSize)` inside `w`. -/
theorem toNat_truncateBits_bvOfInt_negSucc (w : IntWidth) (m : Nat) :
    (truncateBits w (bvOfInt 128 (Int.negSucc m))).toNat =
      Nat.pow 2 (8 * w.byteSize) - 1 -
        Nat.mod m (Nat.pow 2 (8 * w.byteSize)) := by
  rw [toNat_truncateBits, toNat_bvOfInt_negSucc, intWidthModulus_eq_pow_eight]
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  exact mod_two_pow_sub_succ_mod hw m

/-- Round-trip: wrapping a `BitVec 128` through `bvToInt` and `bvOfInt 128`
recovers the original `BitVec 128`. -/
theorem bvOfInt_128_bvToInt (y : BitVec 128) :
    bvOfInt 128 (bvToInt y) = y := by
  unfold bvToInt
  cases Nat.lt_or_ge (2 * y.toNat) (Nat.pow 2 128) with
  | inl hlt =>
    rw [ite_true_of hlt]
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_bvOfInt_ofNat]
    exact Nat.mod_eq_of_lt y.isLt
  | inr hge =>
    rw [ite_false_of (Nat.not_lt_of_ge hge)]
    have hSubEq : Int.ofNat y.toNat - Int.ofNat (Nat.pow 2 128) =
        Int.negSucc (Nat.pow 2 128 - 1 - y.toNat) := by
      have h1 : Neg.neg (Int.ofNat (Nat.pow 2 128)) =
          Int.negSucc (Nat.pow 2 128 - 1) := by decide
      have h2 : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
      change Int.add (Int.ofNat y.toNat)
        (Neg.neg (Int.ofNat (Nat.pow 2 128))) = _
      rw [h1]
      change Int.subNatNat y.toNat (Nat.succ (Nat.pow 2 128 - 1)) = _
      rw [h2]
      unfold Int.subNatNat
      have hDiff : Nat.pow 2 128 - y.toNat =
          Nat.succ (Nat.pow 2 128 - 1 - y.toNat) := by
        have hPos : 0 < Nat.pow 2 128 - y.toNat := Nat.zero_lt_sub_of_lt y.isLt
        have hCancel := Nat.sub_add_cancel hPos
        rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hCancel
        exact hCancel.symm
      rw [hDiff]
    rw [hSubEq]
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_bvOfInt_negSucc]
    have hRemLt : Nat.pow 2 128 - 1 - y.toNat < Nat.pow 2 128 :=
      Nat.lt_of_le_of_lt (Nat.sub_le (Nat.pow 2 128 - 1) y.toNat)
        (Nat.sub_lt (nat_two_pow_pos 128) Nat.one_pos)
    rw [nat_mod_eq_of_lt hRemLt]
    have hSucc : Nat.succ (Nat.pow 2 128 - 1 - y.toNat) =
        Nat.pow 2 128 - y.toNat := by
      have hPos : 0 < Nat.pow 2 128 - y.toNat := Nat.zero_lt_sub_of_lt y.isLt
      have hC := Nat.sub_add_cancel hPos
      rw [Nat.sub_sub, Nat.add_comm y.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    rw [hSucc]
    exact nat_sub_sub_cancel_of_le (Nat.le_of_lt y.isLt)

/-- Unifying theorem for `truncateScalar`: across every width, signedness, and
integer `value : Int`, `truncateScalar w s value` succeeds with payload
`⟨w, s, truncateBits w (bvOfInt 128 value)⟩`. -/
theorem truncateScalar_val_eq (w : IntWidth) (s : Bool) (value : Int) :
    ∃ lossy : Bool,
      truncateScalar w s value =
        .ok (⟨w, s, truncateBits w (bvOfInt 128 value)⟩, lossy) := by
  unfold truncateScalar
  cases s with
  | false =>
    exact ⟨truncateBits w (bvOfInt 128 value) != bvOfInt 128 value, rfl⟩
  | true =>
    dsimp only
    rw [bvToInt_in_i128_range (bvOfInt 128 value), bvOfInt_128_bvToInt]
    exact ⟨signExtendBits w (truncateBits w (bvOfInt 128 value)) !=
        bvToInt (bvOfInt 128 value), rfl⟩

private theorem intBalance_bvTruncMod (w : IntWidth) (z : Int) :
    Nat.mod
        ((truncateBits w (bvOfInt 128 z)).toNat + intNeg z)
        (Nat.pow 2 (8 * w.byteSize)) =
      Nat.mod (intPos z) (Nat.pow 2 (8 * w.byteSize)) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hM : 0 < M := nat_two_pow_pos _
  cases z with
  | ofNat p =>
    dsimp only [intNeg, intPos]
    rw [Nat.add_zero, toNat_truncateBits_bvOfInt_ofNat, nat_mod_mod]
  | negSucc k =>
    dsimp only [intNeg, intPos]
    rw [toNat_truncateBits_bvOfInt_negSucc]
    have hr : Nat.mod k M ≤ M - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt k hM)
    rw [← mod_add_cancel_right (M - 1 - Nat.mod k M) (k + 1) M]
    have hK1 : Nat.mod (k + 1) M = Nat.mod (Nat.mod k M + 1) M :=
      (mod_add_cancel_left k 1 M).symm
    rw [hK1, mod_add_cancel_right]
    have hSum : M - 1 - Nat.mod k M + (Nat.mod k M + 1) = M := by
      rw [Nat.add_comm (Nat.mod k M) 1,
        ← Nat.add_assoc (M - 1 - Nat.mod k M) 1 (Nat.mod k M),
        Nat.add_comm (M - 1 - Nat.mod k M) 1,
        Nat.add_assoc 1 (M - 1 - Nat.mod k M) (Nat.mod k M),
        Nat.sub_add_cancel hr, Nat.add_comm 1 (M - 1),
        Nat.sub_add_cancel hM]
    rw [hSum, nat_mod_self, nat_zero_mod]

private theorem intBalance_eq_bvTrunc (w : IntWidth) {z : Int} {p n : Nat}
    (h : IntBalance z p n) :
    Nat.mod ((truncateBits w (bvOfInt 128 z)).toNat + n)
        (Nat.pow 2 (8 * w.byteSize)) =
      Nat.mod p (Nat.pow 2 (8 * w.byteSize)) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hM : 0 < M := nat_two_pow_pos _
  have hb := intBalance_bvTruncMod w z
  have hMod : Nat.mod
        (((truncateBits w (bvOfInt 128 z)).toNat + n) + intNeg z) M =
      Nat.mod (p + intNeg z) M := by
    rw [Nat.add_right_comm, ← mod_add_cancel_left
        ((truncateBits w (bvOfInt 128 z)).toNat + intNeg z) n M,
      hb, mod_add_cancel_left, h, Nat.add_comm (intNeg z) p]
  exact nat_mod_cancel_add_right hM hMod

private theorem intBalance_neg (x : Int) :
    IntBalance (Int.neg x) (intNeg x) (intPos x) := by
  cases x with
  | ofNat m =>
    cases m with
    | zero => rfl
    | succ m' =>
      change 0 + (m' + 1) = (m' + 1) + 0
      exact Nat.add_comm 0 (m' + 1)
  | negSucc m =>
    change (m + 1) + 0 = 0 + (m + 1)
    exact Nat.add_comm (m + 1) 0

private theorem intBalance_add (x y : Int) :
    IntBalance (x + y) (intPos x + intPos y) (intNeg x + intNeg y) := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      dsimp only [intPos, intNeg]
      exact intBalance_ofNat (a + b)
    | negSucc b =>
      dsimp only [intPos, intNeg]
      rw [Nat.add_zero, Nat.zero_add]
      exact intBalance_subNatNat a (b + 1)
  | negSucc a =>
    cases y with
    | ofNat b =>
      dsimp only [intPos, intNeg]
      rw [Nat.zero_add, Nat.add_zero]
      change IntBalance (Int.subNatNat b (a + 1)) b (a + 1)
      exact intBalance_subNatNat b (a + 1)
    | negSucc b =>
      dsimp only [IntBalance, intPos, intNeg]
      rw [Nat.zero_add, Nat.add_zero]
      change 0 + (a + 1 + (b + 1)) = (a + b + 1 + 1) + 0
      rw [Nat.zero_add, Nat.add_zero, Nat.add_assoc a 1 (b + 1),
        Nat.add_comm 1 (b + 1), ← Nat.add_assoc a (b + 1) 1,
        ← Nat.add_assoc a b 1]

private theorem intBalance_mul (x y : Int) :
    IntBalance (x * y)
      (intPos x * intPos y + intNeg x * intNeg y)
      (intPos x * intNeg y + intNeg x * intPos y) := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      dsimp only [intPos, intNeg]
      rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      exact intBalance_ofNat (a * b)
    | negSucc b =>
      dsimp only [intPos, intNeg]
      have hP0 : a * 0 + 0 * (b + 1) = 0 := by rw [Nat.mul_zero, Nat.zero_mul]
      have hN0 : a * (b + 1) + 0 * 0 = a * (b + 1) := by
        rw [Nat.zero_mul, Nat.add_zero]
      rw [hP0, hN0]
      cases hm : a * (b + 1) with
      | zero =>
        have hEq : Int.ofNat a * Int.negSucc b = Int.ofNat 0 := by
          change Int.negOfNat (a * (b + 1)) = Int.ofNat 0
          rw [hm]
          rfl
        rw [hEq]
        exact intBalance_ofNat 0
      | succ k =>
        have hEq : Int.ofNat a * Int.negSucc b = Int.negSucc k := by
          change Int.negOfNat (a * (b + 1)) = Int.negSucc k
          rw [hm]
          rfl
        rw [hEq]
        change 0 + (k + 1) = (k + 1) + 0
        exact Nat.add_comm 0 (k + 1)
  | negSucc a =>
    cases y with
    | ofNat b =>
      dsimp only [intPos, intNeg]
      have hP0 : 0 * b + (a + 1) * 0 = 0 := by rw [Nat.zero_mul, Nat.mul_zero]
      have hN0 : 0 * 0 + (a + 1) * b = (a + 1) * b := Nat.zero_add _
      rw [hP0, hN0]
      cases hm : (a + 1) * b with
      | zero =>
        have hEq : Int.negSucc a * Int.ofNat b = Int.ofNat 0 := by
          change Int.negOfNat ((a + 1) * b) = Int.ofNat 0
          rw [hm]
          rfl
        rw [hEq]
        exact intBalance_ofNat 0
      | succ k =>
        have hEq : Int.negSucc a * Int.ofNat b = Int.negSucc k := by
          change Int.negOfNat ((a + 1) * b) = Int.negSucc k
          rw [hm]
          rfl
        rw [hEq]
        change 0 + (k + 1) = (k + 1) + 0
        exact Nat.add_comm 0 (k + 1)
    | negSucc b =>
      dsimp only [intPos, intNeg]
      have hP0 : 0 * 0 + (a + 1) * (b + 1) = (a + 1) * (b + 1) := Nat.zero_add _
      have hN0 : 0 * (b + 1) + (a + 1) * 0 = 0 := by
        rw [Nat.zero_mul, Nat.mul_zero]
      rw [hP0, hN0]
      exact intBalance_ofNat ((a + 1) * (b + 1))

private theorem bvTruncMod_add (w : IntWidth) (a b : Int) :
    (truncateBits w (bvOfInt 128 (a + b))).toNat =
      Nat.mod
        ((truncateBits w (bvOfInt 128 a)).toNat +
          (truncateBits w (bvOfInt 128 b)).toNat)
        (Nat.pow 2 (8 * w.byteSize)) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hM : 0 < M := nat_two_pow_pos _
  have hL : (truncateBits w (bvOfInt 128 (a + b))).toNat < M := by
    rw [toNat_truncateBits, intWidthModulus_eq_pow_eight]
    exact Nat.mod_lt _ hM
  have hEq : Nat.mod ((truncateBits w (bvOfInt 128 (a + b))).toNat +
      (intNeg a + intNeg b)) M =
      Nat.mod (((truncateBits w (bvOfInt 128 a)).toNat +
        (truncateBits w (bvOfInt 128 b)).toNat) + (intNeg a + intNeg b)) M := by
    rw [intBalance_eq_bvTrunc w (intBalance_add a b)]
    rw [add_four_rearrange,
      ← mod_add_cancel_left ((truncateBits w (bvOfInt 128 a)).toNat + intNeg a)
        ((truncateBits w (bvOfInt 128 b)).toNat + intNeg b) M,
      intBalance_bvTruncMod w a, mod_add_cancel_left,
      ← mod_add_cancel_right (intPos a)
        ((truncateBits w (bvOfInt 128 b)).toNat + intNeg b) M,
      intBalance_bvTruncMod w b, mod_add_cancel_right]
  have hCanc := nat_mod_cancel_add_right hM hEq
  rw [nat_mod_eq_of_lt hL] at hCanc
  exact hCanc

private theorem bvTruncMod_neg (w : IntWidth) (a : Int) :
    (truncateBits w (bvOfInt 128 (Int.neg a))).toNat =
      Nat.mod
        (Nat.pow 2 (8 * w.byteSize) -
          (truncateBits w (bvOfInt 128 a)).toNat)
        (Nat.pow 2 (8 * w.byteSize)) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hM : 0 < M := nat_two_pow_pos _
  have haLt : (truncateBits w (bvOfInt 128 a)).toNat < M := by
    rw [toNat_truncateBits, intWidthModulus_eq_pow_eight]
    exact Nat.mod_lt _ hM
  have hnLt : (truncateBits w (bvOfInt 128 (Int.neg a))).toNat < M := by
    rw [toNat_truncateBits, intWidthModulus_eq_pow_eight]
    exact Nat.mod_lt _ hM
  have hEq : Nat.mod ((truncateBits w (bvOfInt 128 (Int.neg a))).toNat +
      (truncateBits w (bvOfInt 128 a)).toNat) M =
      Nat.mod ((M - (truncateBits w (bvOfInt 128 a)).toNat) +
        (truncateBits w (bvOfInt 128 a)).toNat) M := by
    rw [Nat.sub_add_cancel (Nat.le_of_lt haLt), nat_mod_self]
    have hCancel :
        Nat.mod (((truncateBits w (bvOfInt 128 (Int.neg a))).toNat +
          (truncateBits w (bvOfInt 128 a)).toNat) + intPos a) M =
        Nat.mod (0 + intPos a) M := by
      rw [Nat.add_right_comm, ← mod_add_cancel_left
          ((truncateBits w (bvOfInt 128 (Int.neg a))).toNat + intPos a) _ M,
        intBalance_eq_bvTrunc w (intBalance_neg a),
        mod_add_cancel_left, Nat.add_comm (intNeg a) _,
        intBalance_bvTruncMod w a, Nat.zero_add]
    exact nat_mod_cancel_add_right hM hCancel
  have hCanc := nat_mod_cancel_add_right hM hEq
  rw [nat_mod_eq_of_lt hnLt] at hCanc
  exact hCanc

private theorem bvTruncMod_sub (w : IntWidth) (a b : Int) :
    (truncateBits w (bvOfInt 128 (a - b))).toNat =
      Nat.mod
        ((Nat.pow 2 (8 * w.byteSize) -
            (truncateBits w (bvOfInt 128 b)).toNat) +
          (truncateBits w (bvOfInt 128 a)).toNat)
        (Nat.pow 2 (8 * w.byteSize)) := by
  change (truncateBits w (bvOfInt 128 (a + Int.neg b))).toNat = _
  rw [bvTruncMod_add, bvTruncMod_neg, mod_add_cancel_right, Nat.add_comm]

private theorem bvTruncMod_mul (w : IntWidth) (a b : Int) :
    (truncateBits w (bvOfInt 128 (a * b))).toNat =
      Nat.mod
        ((truncateBits w (bvOfInt 128 a)).toNat *
          (truncateBits w (bvOfInt 128 b)).toNat)
        (Nat.pow 2 (8 * w.byteSize)) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hM : 0 < M := nat_two_pow_pos _
  have hL : (truncateBits w (bvOfInt 128 (a * b))).toNat < M := by
    rw [toNat_truncateBits, intWidthModulus_eq_pow_eight]
    exact Nat.mod_lt _ hM
  let ax := (truncateBits w (bvOfInt 128 a)).toNat
  let bx := (truncateBits w (bvOfInt 128 b)).toNat
  let cross := intPos a * intNeg b + intNeg a * intPos b
  have haMod : Nat.mod (ax + intNeg a) M = Nat.mod (intPos a) M :=
    intBalance_bvTruncMod w a
  have hbMod : Nat.mod (bx + intNeg b) M = Nat.mod (intPos b) M :=
    intBalance_bvTruncMod w b
  have hProdMod : Nat.mod ((ax + intNeg a) * (bx + intNeg b)) M =
      Nat.mod (intPos a * intPos b) M := by
    rw [← mod_mul_cancel_left (ax + intNeg a) (bx + intNeg b) M, haMod,
      mod_mul_cancel_left, ← mod_mul_cancel_right (intPos a) (bx + intNeg b) M,
      hbMod, mod_mul_cancel_right]
  have hC1 : Nat.mod ((ax + intNeg a) * intNeg b) M =
      Nat.mod (intPos a * intNeg b) M := by
    rw [← mod_mul_cancel_left (ax + intNeg a) (intNeg b) M, haMod,
      mod_mul_cancel_left]
  have hC2 : Nat.mod (intNeg a * (bx + intNeg b)) M =
      Nat.mod (intNeg a * intPos b) M := by
    rw [← mod_mul_cancel_right (intNeg a) (bx + intNeg b) M, hbMod,
      mod_mul_cancel_right]
  have hAlg : ax * bx + (ax + intNeg a) * intNeg b + intNeg a * (bx + intNeg b) =
      (ax + intNeg a) * (bx + intNeg b) + intNeg a * intNeg b := by
    rw [Nat.add_mul ax (intNeg a) (intNeg b)]
    rw [Nat.add_mul ax (intNeg a) (bx + intNeg b)]
    rw [Nat.mul_add ax bx (intNeg b)]
    rw [Nat.mul_add (intNeg a) bx (intNeg b)]
    rw [← Nat.add_assoc (ax * bx) (ax * intNeg b) (intNeg a * intNeg b)]
    exact Nat.add_right_comm (ax * bx + ax * intNeg b) (intNeg a * intNeg b)
      (intNeg a * bx + intNeg a * intNeg b)
  have hEq : Nat.mod ((truncateBits w (bvOfInt 128 (a * b))).toNat + cross) M =
      Nat.mod (ax * bx + cross) M := by
    rw [intBalance_eq_bvTrunc w (intBalance_mul a b)]
    rw [← mod_add_cancel_right (ax * bx) cross M]
    have hCrossEq : Nat.mod ((ax + intNeg a) * intNeg b +
        intNeg a * (bx + intNeg b)) M = Nat.mod cross M := by
      rw [← mod_add_cancel_left ((ax + intNeg a) * intNeg b) _ M, hC1,
        mod_add_cancel_left, ← mod_add_cancel_right (intPos a * intNeg b) _ M,
        hC2, mod_add_cancel_right]
    rw [← hCrossEq, mod_add_cancel_right, ← Nat.add_assoc, hAlg,
      ← mod_add_cancel_left ((ax + intNeg a) * (bx + intNeg b)) _ M, hProdMod,
      mod_add_cancel_left]
  have hCanc := nat_mod_cancel_add_right hM hEq
  rw [nat_mod_eq_of_lt hL] at hCanc
  exact hCanc

private theorem bvExtractLsb_zero_bvZeroExtend (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    (bvExtractLsb (w.bitWidth - 1) 0 (bvZeroExtend 128 x)).toNat = x.toNat := by
  unfold bvExtractLsb bvExtractLsb'
  rw [Anneal.BitVec.toNat_ofNat]
  change Nat.mod (bvZeroExtend 128 x).toNat
      (Nat.pow 2 (w.bitWidth - 1 - 0 + 1)) = x.toNat
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  rw [toNat_bvZeroExtend_of_le hw x]
  have hW : w.bitWidth - 1 - 0 + 1 = w.bitWidth := by
    rw [Nat.sub_zero, Nat.sub_add_cancel (intWidth_bitWidth_pos w)]
  rw [hW, intWidth_bitWidth_eq_eight_mul]
  exact nat_mod_eq_of_lt x.isLt

/-- Unsigned `decodeScalar` of `bvToScalar w false x` equals
`Int.ofNat x.toNat`. -/
theorem decodeScalar_unsigned_eq (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    decodeScalar (bvToScalar w false x) = Int.ofNat x.toNat := by
  unfold decodeScalar
  dsimp only
  rw [bvToScalar_signed, if_false_eq]
  unfold bvToScalar
  dsimp only
  rw [truncateBits_bvZeroExtend]
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  rw [toNat_bvZeroExtend_of_le hw]

/-- Signed `decodeScalar` of `bvToScalar w true x` when `msb x = false` equals
`Int.ofNat x.toNat`. -/
theorem decodeScalar_signed_of_msb_false {w : IntWidth}
    {x : BitVec (8 * w.byteSize)} (hm : Anneal.BitVecArith.msb x = false) :
    decodeScalar (bvToScalar w true x) = Int.ofNat x.toNat := by
  unfold decodeScalar bvToScalar signExtendBits bvSignExtend
  dsimp only
  rw [truncateBits_bvZeroExtend]
  let low := bvExtractLsb (w.bitWidth - 1) 0 (bvZeroExtend 128 x)
  have hLow : low.toNat = x.toNat := bvExtractLsb_zero_bvZeroExtend w x
  have hwPos : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hLtHalf : x.toNat < Nat.pow 2 (8 * w.byteSize - 1) :=
    (Anneal.BitVecArith.msb_eq_false_iff hwPos x).1 hm
  have hW1 : w.bitWidth - 1 - 0 + 1 = w.bitWidth := by
    rw [Nat.sub_zero, Nat.sub_add_cancel (intWidth_bitWidth_pos w)]
  have hCmp1 : 2 * low.toNat < Nat.pow 2 (w.bitWidth - 1 - 0 + 1) := by
    rw [hLow, hW1, intWidth_bitWidth_eq_eight_mul]
    have hEqPow : Nat.pow 2 (8 * w.byteSize) =
        2 * Nat.pow 2 (8 * w.byteSize - 1) := by
      have hw : 8 * w.byteSize = (8 * w.byteSize - 1) + 1 :=
        (Nat.sub_add_cancel hwPos).symm
      have hP := congrArg (Nat.pow 2) hw
      rw [nat_pow_succ, Nat.mul_comm (Nat.pow 2 (8 * w.byteSize - 1)) 2] at hP
      exact hP
    rw [hEqPow]
    exact Nat.mul_lt_mul_of_pos_left hLtHalf (by decide : 0 < 2)
  have hBv1 : bvToInt low = Int.ofNat x.toNat := by
    unfold bvToInt
    rw [ite_true_of hCmp1, hLow]
  change bvToInt (bvOfInt 128 (bvToInt low)) = Int.ofNat x.toNat
  rw [hBv1]
  have hLt127 : x.toNat < Nat.pow 2 127 := by
    have hLe : 8 * w.byteSize - 1 ≤ 127 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact Nat.sub_le_sub_right (intWidth_bitWidth_le_128 w) 1
    exact Nat.lt_of_lt_of_le hLtHalf
      (Nat.pow_le_pow_right (by decide : 0 < 2) hLe)
  have hMod128 : (bvOfInt 128 (Int.ofNat x.toNat)).toNat = x.toNat := by
    rw [toNat_bvOfInt_ofNat]
    exact nat_mod_eq_of_lt (Nat.lt_trans hLt127 (by decide))
  have hCmp2 :
      2 * (bvOfInt 128 (Int.ofNat x.toNat)).toNat < Nat.pow 2 128 := by
    rw [hMod128]
    have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
    rw [hPow128]
    exact Nat.mul_lt_mul_of_pos_left hLt127 (by decide : 0 < 2)
  unfold bvToInt
  rw [ite_true_of hCmp2, hMod128]

/-- Signed `decodeScalar` of `bvToScalar w true x` when `msb x = true` equals
`Int.negSucc (2^(8 * w.byteSize) - 1 - x.toNat)`. -/
theorem decodeScalar_signed_of_msb_true {w : IntWidth}
    {x : BitVec (8 * w.byteSize)} (hm : Anneal.BitVecArith.msb x = true) :
    decodeScalar (bvToScalar w true x) =
      Int.negSucc (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) := by
  unfold decodeScalar bvToScalar signExtendBits bvSignExtend
  dsimp only
  rw [truncateBits_bvZeroExtend]
  let low := bvExtractLsb (w.bitWidth - 1) 0 (bvZeroExtend 128 x)
  have hLow : low.toNat = x.toNat := bvExtractLsb_zero_bvZeroExtend w x
  have hwPos : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  have hGeHalf : Nat.pow 2 (8 * w.byteSize - 1) ≤ x.toNat :=
    (Anneal.BitVecArith.msb_eq_true_iff hwPos x).1 hm
  have hW1 : w.bitWidth - 1 - 0 + 1 = w.bitWidth := by
    rw [Nat.sub_zero, Nat.sub_add_cancel (intWidth_bitWidth_pos w)]
  have hEqPow : Nat.pow 2 (8 * w.byteSize) =
      2 * Nat.pow 2 (8 * w.byteSize - 1) := by
    have hw : 8 * w.byteSize = (8 * w.byteSize - 1) + 1 :=
      (Nat.sub_add_cancel hwPos).symm
    have hP := congrArg (Nat.pow 2) hw
    rw [nat_pow_succ, Nat.mul_comm (Nat.pow 2 (8 * w.byteSize - 1)) 2] at hP
    exact hP
  have hCmp1 : ¬ (2 * low.toNat < Nat.pow 2 (w.bitWidth - 1 - 0 + 1)) := by
    rw [hLow, hW1, intWidth_bitWidth_eq_eight_mul, hEqPow]
    exact Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hGeHalf)
  have hSubNat :
      Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 (8 * w.byteSize)) =
        Int.negSucc (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) := by
    have hPosW : 0 < Nat.pow 2 (8 * w.byteSize) := nat_two_pow_pos _
    rw [int_ofNat_sub_ofNat]
    unfold Int.subNatNat
    have hDiff : Nat.pow 2 (8 * w.byteSize) - x.toNat =
        Nat.succ (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) := by
      have hPosD : 0 < Nat.pow 2 (8 * w.byteSize) - x.toNat :=
        Nat.zero_lt_sub_of_lt x.isLt
      have hC := Nat.sub_add_cancel hPosD
      rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
      exact hC.symm
    rw [hDiff]
  have hBv1 : bvToInt low =
      Int.negSucc (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) := by
    unfold bvToInt
    rw [ite_false_of hCmp1, hLow, hW1, intWidth_bitWidth_eq_eight_mul]
    exact hSubNat
  change bvToInt (bvOfInt 128 (bvToInt low)) = _
  rw [hBv1]
  let d := Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat
  have hdLtHalf : d < Nat.pow 2 (8 * w.byteSize - 1) := by
    let H := Nat.pow 2 (8 * w.byteSize - 1)
    have hH : 0 < H := nat_two_pow_pos _
    have hPowSum : Nat.pow 2 (8 * w.byteSize) = H + H := by
      rw [hEqPow, Nat.two_mul]
    have hDx : d + x.toNat = Nat.pow 2 (8 * w.byteSize) - 1 := by
      exact Nat.sub_add_cancel (Nat.le_sub_one_of_lt x.isLt)
    have hLtH : d + H < H + H := by
      have h1 : d + H ≤ d + x.toNat := Nat.add_le_add_left hGeHalf d
      rw [hDx] at h1
      exact Nat.lt_of_le_of_lt h1 (by
        rw [hPowSum]
        exact Nat.sub_lt (Nat.lt_of_lt_of_le hH (Nat.le_add_right H H))
          Nat.one_pos)
    exact nat_lt_of_add_lt_add_right hLtH
  have hdLt127 : d < Nat.pow 2 127 := by
    have hLe : 8 * w.byteSize - 1 ≤ 127 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact Nat.sub_le_sub_right (intWidth_bitWidth_le_128 w) 1
    exact Nat.lt_of_lt_of_le hdLtHalf
      (Nat.pow_le_pow_right (by decide : 0 < 2) hLe)
  have hdLt128 : d < Nat.pow 2 128 := Nat.lt_trans hdLt127 (by decide)
  have hToNat2 : (bvOfInt 128 (Int.negSucc d)).toNat =
      Nat.pow 2 128 - Nat.succ d := by
    rw [toNat_bvOfInt_negSucc, nat_mod_eq_of_lt hdLt128]
  have hHalf128 : Nat.pow 2 127 ≤ Nat.pow 2 128 - Nat.succ d := by
    have hPow128 : Nat.pow 2 128 = Nat.pow 2 127 + Nat.pow 2 127 := by decide
    have hAdd : Nat.succ d + Nat.pow 2 127 ≤ Nat.pow 2 128 := by
      rw [hPow128]
      exact Nat.add_le_add_right hdLt127 _
    have hSub := Nat.sub_le_sub_right hAdd (Nat.succ d)
    rw [Nat.add_comm (Nat.succ d) (Nat.pow 2 127), Nat.add_sub_cancel] at hSub
    exact hSub
  have hCmp2 :
      ¬ (2 * (bvOfInt 128 (Int.negSucc d)).toNat < Nat.pow 2 128) := by
    rw [hToNat2]
    have hPow128 : Nat.pow 2 128 = 2 * Nat.pow 2 127 := by decide
    rw [hPow128]
    exact Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hHalf128)
  unfold bvToInt
  rw [ite_false_of hCmp2, hToNat2]
  have hNeg128 : Neg.neg (Int.ofNat (Nat.pow 2 128)) =
      Int.negSucc (Nat.pow 2 128 - 1) := by decide
  have hSucc128 : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
  change Int.add (Int.ofNat (Nat.pow 2 128 - Nat.succ d))
    (Neg.neg (Int.ofNat (Nat.pow 2 128))) = Int.negSucc d
  rw [hNeg128]
  change Int.subNatNat (Nat.pow 2 128 - Nat.succ d)
    (Nat.succ (Nat.pow 2 128 - 1)) = Int.negSucc d
  rw [hSucc128]
  unfold Int.subNatNat
  have hFinal : Nat.pow 2 128 - (Nat.pow 2 128 - Nat.succ d) = Nat.succ d :=
    nat_sub_sub_cancel_of_le (Nat.succ_le_of_lt hdLt128)
  rw [hFinal]

private theorem intBalance_decodeScalar_signed (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    IntBalance (decodeScalar (bvToScalar w true x))
      (Anneal.BitVecArith.signedKey x) (Nat.pow 2 (8 * w.byteSize - 1)) := by
  have hwPos : 0 < 8 * w.byteSize := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_pos w
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    rw [decodeScalar_signed_of_msb_false hm,
      Anneal.BitVecArith.signedKey_eq_of_msb_false hwPos hm]
    dsimp only [IntBalance, intPos, intNeg]
    rw [Nat.zero_add]
  | true =>
    rw [decodeScalar_signed_of_msb_true hm,
      Anneal.BitVecArith.signedKey_eq_of_msb_true hwPos hm]
    have hGe := (Anneal.BitVecArith.msb_eq_true_iff hwPos x).1 hm
    dsimp only [IntBalance, intPos, intNeg]
    rw [Nat.zero_add]
    have hSucc : Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat + 1 =
        Nat.pow 2 (8 * w.byteSize) - x.toNat := by
      have hPosD : 0 < Nat.pow 2 (8 * w.byteSize) - x.toNat :=
        Nat.zero_lt_sub_of_lt x.isLt
      have hC := Nat.sub_add_cancel hPosD
      rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hC
      exact hC
    rw [hSucc]
    have hEqPow : Nat.pow 2 (8 * w.byteSize) =
        Nat.pow 2 (8 * w.byteSize - 1) + Nat.pow 2 (8 * w.byteSize - 1) := by
      have hw : 8 * w.byteSize = (8 * w.byteSize - 1) + 1 :=
        (Nat.sub_add_cancel hwPos).symm
      have hP := congrArg (Nat.pow 2) hw
      rw [nat_pow_succ, Nat.mul_two] at hP
      exact hP
    have hRhs : (Nat.pow 2 (8 * w.byteSize) - x.toNat) + x.toNat =
        Nat.pow 2 (8 * w.byteSize) :=
      Nat.sub_add_cancel (Nat.le_of_lt x.isLt)
    have hFin : (Nat.pow 2 (8 * w.byteSize) - x.toNat) +
        (x.toNat - Nat.pow 2 (8 * w.byteSize - 1)) =
        Nat.pow 2 (8 * w.byteSize - 1) := by
      have hA : ((Nat.pow 2 (8 * w.byteSize) - x.toNat) +
          (x.toNat - Nat.pow 2 (8 * w.byteSize - 1))) +
          Nat.pow 2 (8 * w.byteSize - 1) =
          Nat.pow 2 (8 * w.byteSize - 1) +
            Nat.pow 2 (8 * w.byteSize - 1) := by
        rw [Nat.add_assoc, Nat.sub_add_cancel hGe, hRhs, hEqPow]
      exact Nat.add_right_cancel hA
    exact hFin.symm

private theorem intBalance_lt_iff {a b : Int} {pa na pb nb : Nat}
    (ha : IntBalance a pa na) (hb : IntBalance b pb nb) (hN : na = nb) :
    a < b ↔ pa < pb := by
  subst hN
  unfold IntBalance at ha hb
  cases a with
  | ofNat ma =>
    cases b with
    | ofNat mb =>
      dsimp only [intPos, intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      have h1 : ma < mb ↔ ma + na < mb + na :=
        ⟨fun h => Nat.add_lt_add_right h na,
         fun h => nat_lt_of_add_lt_add_right h⟩
      rw [ha, hb] at h1
      rw [int_ofNat_lt_iff]
      exact h1
    | negSucc mb =>
      dsimp only [intPos, intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      have hGt : pb < pa := by
        have h1 : (mb + 1) + pb = na := hb.symm
        have h2 : na < ma + na + (mb + 1) := by
          have hPos : 0 < mb + 1 := Nat.zero_lt_succ mb
          exact Nat.lt_of_le_of_lt (Nat.le_add_left na ma)
            (Nat.lt_add_of_pos_right hPos)
        rw [Nat.add_comm (ma + na) (mb + 1), ha, ← h1] at h2
        rw [Nat.add_comm (mb + 1) pb, Nat.add_comm (mb + 1) pa] at h2
        exact nat_lt_of_add_lt_add_right h2
      constructor
      · intro hF
        exact False.elim (nomatch hF)
      · intro hLt
        exact False.elim (Nat.lt_asymm hLt hGt)
  | negSucc ma =>
    cases b with
    | ofNat mb =>
      dsimp only [intPos, intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      have hLt : pa < pb := by
        have h1 : (ma + 1) + pa = na := ha.symm
        have h2 : na < mb + na + (ma + 1) := by
          have hPos : 0 < ma + 1 := Nat.zero_lt_succ ma
          exact Nat.lt_of_le_of_lt (Nat.le_add_left na mb)
            (Nat.lt_add_of_pos_right hPos)
        rw [Nat.add_comm (mb + na) (ma + 1), hb, ← h1] at h2
        rw [Nat.add_comm (ma + 1) pa, Nat.add_comm (ma + 1) pb] at h2
        exact nat_lt_of_add_lt_add_right h2
      constructor
      · intro _
        exact hLt
      · intro _
        exact int_negSucc_lt_ofNat ma mb
    | negSucc mb =>
      dsimp only [intPos, intNeg] at ha hb
      rw [Nat.zero_add] at ha hb
      have hEq : (ma + 1) + pa = (mb + 1) + pb := ha.symm.trans hb
      have hIff : pa < pb ↔ mb + 1 < ma + 1 := by
        constructor
        · intro h
          have h2 : (mb + 1) + pa < (mb + 1) + pb :=
            Nat.add_lt_add_left h (mb + 1)
          rw [← hEq] at h2
          exact nat_lt_of_add_lt_add_right h2
        · intro h
          have h2 : pa + (mb + 1) < pa + (ma + 1) :=
            Nat.add_lt_add_left h pa
          rw [Nat.add_comm pa (ma + 1), hEq, Nat.add_comm (mb + 1) pb] at h2
          exact nat_lt_of_add_lt_add_right h2
      constructor
      · intro hInt
        have h2 : mb + 1 < ma + 1 :=
          Nat.succ_lt_succ (int_negSucc_lt_negSucc_iff.mp hInt)
        exact hIff.mpr h2
      · intro hPa
        have hMa : mb + 1 < ma + 1 := hIff.mp hPa
        exact int_negSucc_lt_negSucc_iff.mpr (Nat.lt_of_succ_lt_succ hMa)

private theorem int_not_lt_iff_le (a b : Int) : ¬ (a < b) ↔ b ≤ a := by
  cases a with
  | ofNat ma =>
    cases b with
    | ofNat mb =>
      rw [int_ofNat_lt_iff, Nat.not_lt, int_ofNat_le_iff]
    | negSucc mb =>
      constructor
      · intro _; exact int_negSucc_le_ofNat mb ma
      · intro _ hF; nomatch hF
  | negSucc ma =>
    cases b with
    | ofNat mb =>
      constructor
      · intro hF; exact False.elim (hF (int_negSucc_lt_ofNat ma mb))
      · intro hF; exact False.elim (int_not_ofNat_le_negSucc mb ma hF)
    | negSucc mb =>
      rw [int_negSucc_lt_negSucc_iff, Nat.not_lt, int_negSucc_le_negSucc_iff]

private theorem intBalance_le_iff {a b : Int} {pa na pb nb : Nat}
    (ha : IntBalance a pa na) (hb : IntBalance b pb nb) (hN : na = nb) :
    a ≤ b ↔ pa ≤ pb := by
  have hGt := intBalance_lt_iff hb ha hN.symm
  rw [← int_not_lt_iff_le b a, hGt, Nat.not_lt]

/-- Signed `<` on `decodeScalar` agrees exactly with `Anneal.BitVecArith.slt`.
-/
theorem decodeScalar_lt_iff_slt {w : IntWidth}
    (x y : BitVec (8 * w.byteSize)) :
    decodeScalar (bvToScalar w true x) < decodeScalar (bvToScalar w true y) ↔
      Anneal.BitVecArith.slt x y :=
  intBalance_lt_iff (intBalance_decodeScalar_signed w x)
    (intBalance_decodeScalar_signed w y) rfl

/-- Signed `≤` on `decodeScalar` agrees exactly with `Anneal.BitVecArith.sle`.
-/
theorem decodeScalar_le_iff_sle {w : IntWidth}
    (x y : BitVec (8 * w.byteSize)) :
    decodeScalar (bvToScalar w true x) ≤ decodeScalar (bvToScalar w true y) ↔
      Anneal.BitVecArith.sle x y :=
  intBalance_le_iff (intBalance_decodeScalar_signed w x)
    (intBalance_decodeScalar_signed w y) rfl

/-- `decodeScalar` is injective on `bvToScalar w s` across both signedness
modes. -/
theorem decodeScalar_eq_iff (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    decodeScalar (bvToScalar w s x) = decodeScalar (bvToScalar w s y) ↔
      x = y := by
  cases s with
  | false =>
    rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
    constructor
    · intro h
      exact Anneal.BitVec.eq_of_toNat_eq (Int.ofNat.inj h)
    · intro h
      rw [h]
  | true =>
    constructor
    · intro h
      have hle1 : Anneal.BitVecArith.sle x y :=
        (decodeScalar_le_iff_sle x y).mp (by rw [h]; exact int_le_refl _)
      have hle2 : Anneal.BitVecArith.sle y x :=
        (decodeScalar_le_iff_sle y x).mp (by rw [h]; exact int_le_refl _)
      exact Anneal.BitVecArith.sle_antisymm hle1 hle2
    · intro h
      rw [h]

private theorem truncateBits_bvOfInt_decode (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    (truncateBits w (bvOfInt 128 (decodeScalar (bvToScalar w s x)))).toNat =
      x.toNat := by
  cases s with
  | false =>
    rw [decodeScalar_unsigned_eq, toNat_truncateBits_bvOfInt_ofNat]
    exact nat_mod_eq_of_lt x.isLt
  | true =>
    cases hm : Anneal.BitVecArith.msb x with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm, toNat_truncateBits_bvOfInt_ofNat]
      exact nat_mod_eq_of_lt x.isLt
    | true =>
      rw [decodeScalar_signed_of_msb_true hm, toNat_truncateBits_bvOfInt_negSucc]
      have hDlt : Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat <
          Nat.pow 2 (8 * w.byteSize) :=
        Nat.lt_of_le_of_lt (Nat.sub_le (Nat.pow 2 (8 * w.byteSize) - 1) x.toNat)
          (Nat.sub_lt (nat_two_pow_pos _) Nat.one_pos)
      rw [nat_mod_eq_of_lt hDlt]
      exact nat_sub_sub_cancel_of_le (Nat.le_sub_one_of_lt x.isLt)

/-! ## 3. Operational `evalBinOp`, `evalUnOp`, and `evalIntToIntCast` Bridges -/

private theorem evalBinOp_header_eq (w : IntWidth) (s : Bool) :
    (!(IntWidth.beq w w && (s == s))) = false := by
  cases w <;> cases s <;> rfl

/-- `evalBinOp .bitAnd` on `bvToScalar w s` computes `Anneal.BitVec.and`. -/
theorem evalBinOp_bitAnd_eq_and (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .bitAnd (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.scalar (bvToScalar w s (Anneal.BitVec.and x y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  dsimp only [bvToScalar_width, bvToScalar_signed]
  dsimp only [bvToScalar]
  rw [truncateBits_bvZeroExtend, truncateBits_bvZeroExtend, bvAnd_eq_and]
  have hAnd :
      truncateBits w
          (Anneal.BitVec.and (bvZeroExtend 128 x) (bvZeroExtend 128 y)) =
        bvZeroExtend 128 (Anneal.BitVec.and x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits, Anneal.BitVec.toNat_and,
      toNat_bvZeroExtend_of_le hw x, toNat_bvZeroExtend_of_le hw y,
      toNat_bvZeroExtend_of_le hw (Anneal.BitVec.and x y),
      intWidthModulus_eq_pow_eight, Anneal.BitVec.toNat_and]
    exact nat_mod_eq_of_lt (Anneal.BitVec.and x y).isLt
  rw [hAnd]

/-- `evalBinOp .bitOr` on `bvToScalar w s` computes `Anneal.BitVec.or`. -/
theorem evalBinOp_bitOr_eq_or (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .bitOr (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.scalar (bvToScalar w s (Anneal.BitVec.or x y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  dsimp only [bvToScalar_width, bvToScalar_signed]
  dsimp only [bvToScalar]
  rw [truncateBits_bvZeroExtend, truncateBits_bvZeroExtend, bvOr_eq_or]
  have hOr :
      truncateBits w
          (Anneal.BitVec.or (bvZeroExtend 128 x) (bvZeroExtend 128 y)) =
        bvZeroExtend 128 (Anneal.BitVec.or x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits, Anneal.BitVec.toNat_or,
      toNat_bvZeroExtend_of_le hw x, toNat_bvZeroExtend_of_le hw y,
      toNat_bvZeroExtend_of_le hw (Anneal.BitVec.or x y),
      intWidthModulus_eq_pow_eight, Anneal.BitVec.toNat_or]
    exact nat_mod_eq_of_lt (Anneal.BitVec.or x y).isLt
  rw [hOr]

/-- `evalBinOp .bitXor` on `bvToScalar w s` computes `Anneal.BitVec.xor`. -/
theorem evalBinOp_bitXor_eq_xor (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .bitXor (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.scalar (bvToScalar w s (Anneal.BitVec.xor x y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  dsimp only [bvToScalar_width, bvToScalar_signed]
  dsimp only [bvToScalar]
  rw [truncateBits_bvZeroExtend, truncateBits_bvZeroExtend, bvXor_eq_xor]
  have hXor :
      truncateBits w
          (Anneal.BitVec.xor (bvZeroExtend 128 x) (bvZeroExtend 128 y)) =
        bvZeroExtend 128 (Anneal.BitVec.xor x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits, Anneal.BitVec.toNat_xor,
      toNat_bvZeroExtend_of_le hw x, toNat_bvZeroExtend_of_le hw y,
      toNat_bvZeroExtend_of_le hw (Anneal.BitVec.xor x y),
      intWidthModulus_eq_pow_eight, Anneal.BitVec.toNat_xor]
    exact nat_mod_eq_of_lt (Anneal.BitVec.xor x y).isLt
  rw [hXor]

/-- `evalBinOp .add` on both unsigned and signed scalars computes wrapping
bitvector addition `x + y`. -/
theorem evalBinOp_add_eq_add (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .add (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.scalar (bvToScalar w s (x + y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  change evalArithOp .add w s (decodeScalar (bvToScalar w s x))
    (decodeScalar (bvToScalar w s y)) = _
  refine (if_bool_false ((congrArg (· && _) (Bool.and_false s)).trans
    (Bool.false_and _))).trans ?_
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (decodeScalar (bvToScalar w s x) + decodeScalar (bvToScalar w s y))
  rw [hTrunc]
  have hBits : truncateBits w (bvOfInt 128
        (decodeScalar (bvToScalar w s x) + decodeScalar (bvToScalar w s y))) =
      bvZeroExtend 128 (x + y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [bvTruncMod_add, truncateBits_bvOfInt_decode,
      truncateBits_bvOfInt_decode, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_add]
  exact (if_bool_false (Bool.and_false _)).trans
    (congrArg (fun b => Except.ok (Val.scalar ⟨w, s, b⟩)) hBits)

/-- `evalBinOp .sub` on both unsigned and signed scalars computes wrapping
bitvector subtraction `x - y`. -/
theorem evalBinOp_sub_eq_sub (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .sub (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.scalar (bvToScalar w s (x - y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  change evalArithOp .sub w s (decodeScalar (bvToScalar w s x))
    (decodeScalar (bvToScalar w s y)) = _
  refine (if_bool_false ((congrArg (· && _) (Bool.and_false s)).trans
    (Bool.false_and _))).trans ?_
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (decodeScalar (bvToScalar w s x) - decodeScalar (bvToScalar w s y))
  rw [hTrunc]
  have hBits : truncateBits w (bvOfInt 128
        (decodeScalar (bvToScalar w s x) - decodeScalar (bvToScalar w s y))) =
      bvZeroExtend 128 (x - y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [bvTruncMod_sub, truncateBits_bvOfInt_decode,
      truncateBits_bvOfInt_decode, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_sub]
  exact (if_bool_false (Bool.and_false _)).trans
    (congrArg (fun b => Except.ok (Val.scalar ⟨w, s, b⟩)) hBits)

/-- `evalBinOp .mul` on both unsigned and signed scalars computes wrapping
bitvector multiplication `Anneal.BitVec.mul x y`. -/
theorem evalBinOp_mul_eq_mul (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .mul (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.scalar (bvToScalar w s (Anneal.BitVec.mul x y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  change evalArithOp .mul w s (decodeScalar (bvToScalar w s x))
    (decodeScalar (bvToScalar w s y)) = _
  refine (if_bool_false ((congrArg (· && _) (Bool.and_false s)).trans
    (Bool.false_and _))).trans ?_
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (decodeScalar (bvToScalar w s x) * decodeScalar (bvToScalar w s y))
  rw [hTrunc]
  have hBits : truncateBits w (bvOfInt 128
        (decodeScalar (bvToScalar w s x) * decodeScalar (bvToScalar w s y))) =
      bvZeroExtend 128 (Anneal.BitVec.mul x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [bvTruncMod_mul, truncateBits_bvOfInt_decode,
      truncateBits_bvOfInt_decode, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_mul]
  exact (if_bool_false (Bool.and_false _)).trans
    (congrArg (fun b => Except.ok (Val.scalar ⟨w, s, b⟩)) hBits)

/-- Unsigned `evalBinOp .div` with nonzero divisor computes
`Anneal.BitVec.udiv x y`. -/
theorem evalBinOp_div_unsigned_eq_udiv {w : IntWidth}
    (x : BitVec (8 * w.byteSize)) {y : BitVec (8 * w.byteSize)}
    (hy : y.toNat ≠ 0) :
    evalBinOp .div (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.scalar (bvToScalar w false (Anneal.BitVec.udiv x y))) := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .div w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  have hyEq : (Int.ofNat y.toNat == 0) = false := by
    cases hc : (Int.ofNat y.toNat == (0 : Int)) with
    | false => rfl
    | true => exact False.elim (hy (Int.ofNat.inj (eq_of_beq hc)))
  have hBits : truncateBits w (bvOfInt 128 (Int.ofNat (Nat.div x.toNat y.toNat))) =
      bvZeroExtend 128 (Anneal.BitVec.udiv x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits_bvOfInt_ofNat, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_udiv]
    exact nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)
  exact (if_bool_false hyEq).trans ((if_bool_false (Bool.and_false _)).trans
    (congrArg (fun b => Except.ok (Val.scalar ⟨w, false, b⟩)) hBits))

/-- Unsigned `evalBinOp .div` with zero divisor faults with
`FaultKind.undefined`. -/
theorem evalBinOp_div_unsigned_zero_fault {w : IntWidth}
    (x y : BitVec (8 * w.byteSize)) (hy : y.toNat = 0) :
    evalBinOp .div (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) = .error .undefined := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .div w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq w y, hy]
  rfl

/-- Unsigned `evalBinOp .rem` with nonzero divisor computes
`Anneal.BitVecArith.urem x y`. -/
theorem evalBinOp_rem_unsigned_eq_urem {w : IntWidth}
    (x : BitVec (8 * w.byteSize)) {y : BitVec (8 * w.byteSize)}
    (hy : y.toNat ≠ 0) :
    evalBinOp .rem (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.scalar (bvToScalar w false (Anneal.BitVecArith.urem x y))) := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .rem w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  have hyEq : (Int.ofNat y.toNat == 0) = false := by
    cases hc : (Int.ofNat y.toNat == (0 : Int)) with
    | false => rfl
    | true => exact False.elim (hy (Int.ofNat.inj (eq_of_beq hc)))
  have hBits : truncateBits w (bvOfInt 128 (Int.ofNat (Nat.mod x.toNat y.toNat))) =
      bvZeroExtend 128 (Anneal.BitVecArith.urem x y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits_bvOfInt_ofNat, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVecArith.toNat_urem]
    exact nat_mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)
  exact (if_bool_false hyEq).trans ((if_bool_false (Bool.and_false _)).trans
    (congrArg (fun b => Except.ok (Val.scalar ⟨w, false, b⟩)) hBits))

/-- Unsigned `evalBinOp .rem` with zero divisor faults with
`FaultKind.undefined`. -/
theorem evalBinOp_rem_unsigned_zero_fault {w : IntWidth}
    (x y : BitVec (8 * w.byteSize)) (hy : y.toNat = 0) :
    evalBinOp .rem (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) = .error .undefined := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .rem w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq w y, hy]
  rfl

private theorem unsigned_add_overflow_flag_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    let result := Int.ofNat x.toNat + Int.ofNat y.toNat
    let hostOverflow :=
      decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
    let trunc := truncateBits w (bvOfInt 128 result)
    let lossy := trunc != bvOfInt 128 result
    (hostOverflow || lossy) =
      decide (Nat.pow 2 (8 * w.byteSize) ≤ x.toNat + y.toNat) := by
  let M := Nat.pow 2 (8 * w.byteSize)
  have hNotNeg : decide (Int.ofNat (x.toNat + y.toNat) < 0) = false :=
    decide_eq_false (fun h => nomatch h)
  have hMod : (truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)))).toNat =
      Nat.mod (x.toNat + y.toNat) M := by
    rw [toNat_truncateBits_bvOfInt_ofNat]
  have h128 : (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))).toNat =
      Nat.mod (x.toNat + y.toNat) (Nat.pow 2 128) := toNat_bvOfInt_ofNat 128 _
  cases Nat.lt_or_ge (x.toNat + y.toNat) M with
  | inl hLt =>
    have hLt128 : x.toNat + y.toNat < Nat.pow 2 128 := by
      have hw : 8 * w.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 w
      exact Nat.lt_of_lt_of_le hLt (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
    have hNotGe : ¬ (Int.ofNat (x.toNat + y.toNat) ≥ HPow.hPow (2 : Int) 128) := by
      intro hGe
      have hP : Nat.pow 2 128 ≤ x.toNat + y.toNat :=
        int_ofNat_le_iff.mp (by change Int.ofNat (Nat.pow 2 128) ≤ _; exact hGe)
      exact Nat.not_le_of_gt hLt128 hP
    have hEqBv : truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) =
        bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [hMod, h128, nat_mod_eq_of_lt hLt, nat_mod_eq_of_lt hLt128]
    have hLossyFalse :
        (truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) !=
          bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) = false := by
      change (!(truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) ==
          bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)))) = false
      rw [hEqBv, beq_self_eq_true]
      rfl
    change (decide (Int.ofNat (x.toNat + y.toNat) < 0) ||
        decide (Int.ofNat (x.toNat + y.toNat) ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) !=
          bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)))) =
      decide (M ≤ x.toNat + y.toNat)
    rw [hNotNeg, decide_eq_false hNotGe, hLossyFalse,
      decide_eq_false (Nat.not_le_of_gt hLt)]
    rfl
  | inr hGe =>
    rw [decide_eq_true hGe]
    cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 128) with
    | inl hLt128 =>
      have hNeBv :
          truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) ≠
            bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)) := by
        intro hEq
        have hNat := congrArg BitVec.toNat hEq
        rw [hMod, h128, nat_mod_eq_of_lt hLt128] at hNat
        have hLtM : Nat.mod (x.toNat + y.toNat) M < M :=
          Nat.mod_lt _ (nat_two_pow_pos _)
        rw [hNat] at hLtM
        exact Nat.not_le_of_gt hLtM hGe
      have hLossyTrue :
          (truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) !=
            bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) = true :=
        bne_iff_ne.mpr hNeBv
      change (decide (Int.ofNat (x.toNat + y.toNat) < 0) ||
          decide (Int.ofNat (x.toNat + y.toNat) ≥ HPow.hPow (2 : Int) 128) ||
          (truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) !=
            bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)))) = true
      rw [hLossyTrue, Bool.or_true]
    | inr hGe128 =>
      have hGeI : Int.ofNat (x.toNat + y.toNat) ≥ HPow.hPow (2 : Int) 128 :=
        int_ofNat_le_iff.mpr hGe128
      change (decide (Int.ofNat (x.toNat + y.toNat) < 0) ||
          decide (Int.ofNat (x.toNat + y.toNat) ≥ HPow.hPow (2 : Int) 128) ||
          (truncateBits w (bvOfInt 128 (Int.ofNat (x.toNat + y.toNat))) !=
            bvOfInt 128 (Int.ofNat (x.toNat + y.toNat)))) = true
      rw [decide_eq_true hGeI, Bool.or_true, Bool.true_or]

/-- Unsigned `evalBinOp .addWithOverflow` returns `(x + y, decide (2^(8 *
w.byteSize) ≤ x.toNat + y.toNat))` across all six widths (including `u128`). -/
theorem evalBinOp_addWithOverflow_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .addWithOverflow (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.tuple [
        .scalar (bvToScalar w false (x + y)),
        .bool (decide (Nat.pow 2 (8 * w.byteSize) ≤ x.toNat + y.toNat))
      ]) := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .addWithOverflow w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  have hBits : truncateBits w
        (bvOfInt 128 (Int.ofNat x.toNat + Int.ofNat y.toNat)) =
      bvZeroExtend 128 (x + y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    have hSum : Int.ofNat x.toNat + Int.ofNat y.toNat =
        Int.ofNat (x.toNat + y.toNat) := rfl
    rw [hSum, toNat_truncateBits_bvOfInt_ofNat, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_add]
  exact (if_bool_false (Bool.and_false _)).trans
    ((congrArg (fun f => Except.ok (Val.tuple [Val.scalar ⟨w, false, _⟩,
      Val.bool f])) (unsigned_add_overflow_flag_eq w x y)).trans
    (congrArg (fun b => Except.ok (Val.tuple [Val.scalar ⟨w, false, b⟩,
      Val.bool _])) hBits))

/-- Unsigned `evalBinOp .addUnchecked` succeeds with `x + y` iff
`x.toNat + y.toNat < 2^(8 * w.byteSize)` and faults with `.undefined` otherwise.
-/
theorem evalBinOp_addUnchecked_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .addUnchecked (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      if x.toNat + y.toNat < Nat.pow 2 (8 * w.byteSize) then
        .ok (.scalar (bvToScalar w false (x + y)))
      else
        .error .undefined := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .addUnchecked w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  have hF := (Bool.and_true _).trans (unsigned_add_overflow_flag_eq w x y)
  cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 (8 * w.byteSize)) with
  | inl hLt =>
    have hBits : truncateBits w
          (bvOfInt 128 (Int.ofNat x.toNat + Int.ofNat y.toNat)) =
        bvZeroExtend 128 (x + y) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      have hw : 8 * w.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 w
      have hSum : Int.ofNat x.toNat + Int.ofNat y.toNat =
          Int.ofNat (x.toNat + y.toNat) := rfl
      rw [hSum, toNat_truncateBits_bvOfInt_ofNat, toNat_bvZeroExtend_of_le hw,
        Anneal.BitVec.toNat_add]
    exact (if_bool_false
        (hF.trans (decide_eq_false (Nat.not_le_of_gt hLt)))).trans
      ((congrArg (fun b => Except.ok (Val.scalar ⟨w, false, b⟩)) hBits).trans
        (ite_true_of hLt).symm)
  | inr hGe =>
    exact (if_bool_true (hF.trans (decide_eq_true hGe))).trans
      (ite_false_of (Nat.not_lt_of_ge hGe)).symm

private theorem unsigned_sub_overflow_flag_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    let result := Int.ofNat x.toNat - Int.ofNat y.toNat
    let hostOverflow :=
      decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
    let trunc := truncateBits w (bvOfInt 128 result)
    let lossy := trunc != bvOfInt 128 result
    (hostOverflow || lossy) = decide (x.toNat < y.toNat) := by
  let result := Int.ofNat x.toNat - Int.ofNat y.toNat
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl hLt =>
    have hNeg : result < 0 := by
      change Int.ofNat x.toNat - Int.ofNat y.toNat < 0
      rw [int_ofNat_sub_ofNat]
      unfold Int.subNatNat
      have hSubPos : 0 < y.toNat - x.toNat := Nat.zero_lt_sub_of_lt hLt
      cases hd : y.toNat - x.toNat with
      | zero =>
        rw [hd] at hSubPos
        nomatch hSubPos
      | succ k => exact int_negSucc_lt_zero k
    change (decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 result) != bvOfInt 128 result)) =
      decide (x.toNat < y.toNat)
    rw [decide_eq_true hNeg, Bool.true_or, Bool.true_or, decide_eq_true hLt]
  | inr hGe =>
    have hSub : result = Int.ofNat (x.toNat - y.toNat) := by
      change Int.ofNat x.toNat - Int.ofNat y.toNat = _
      rw [int_ofNat_sub_ofNat]
      unfold Int.subNatNat
      rw [Nat.sub_eq_zero_of_le hGe]
    have hDiffLt : x.toNat - y.toNat < Nat.pow 2 (8 * w.byteSize) :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
    have hDiffLt128 : x.toNat - y.toNat < Nat.pow 2 128 := by
      have hw : 8 * w.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 w
      exact Nat.lt_of_lt_of_le hDiffLt (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
    have hNotNeg : ¬ (result < 0) := by
      rw [hSub]
      intro hF
      nomatch hF
    have hNotGe : ¬ (result ≥ HPow.hPow (2 : Int) 128) := by
      rw [hSub]
      intro hGeI
      exact Nat.not_le_of_gt hDiffLt128
        (int_ofNat_le_iff.mp (by change Int.ofNat (Nat.pow 2 128) ≤ _; exact hGeI))
    have hEqBv : truncateBits w (bvOfInt 128 result) = bvOfInt 128 result := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [hSub, toNat_truncateBits_bvOfInt_ofNat, toNat_bvOfInt_ofNat,
        nat_mod_eq_of_lt hDiffLt, nat_mod_eq_of_lt hDiffLt128]
    have hLossyFalse : (truncateBits w (bvOfInt 128 result) !=
        bvOfInt 128 result) = false := by
      change (!(truncateBits w (bvOfInt 128 result) ==
          bvOfInt 128 result)) = false
      rw [hEqBv, beq_self_eq_true]
      rfl
    change (decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128) ||
        (truncateBits w (bvOfInt 128 result) != bvOfInt 128 result)) =
      decide (x.toNat < y.toNat)
    rw [decide_eq_false hNotNeg, decide_eq_false hNotGe, hLossyFalse,
      decide_eq_false (Nat.not_lt_of_ge hGe)]
    rfl

/-- Unsigned `evalBinOp .subWithOverflow` returns `(x - y, decide (x.toNat <
y.toNat))`. -/
theorem evalBinOp_subWithOverflow_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .subWithOverflow (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.tuple [
        .scalar (bvToScalar w false (x - y)),
        .bool (decide (x.toNat < y.toNat))
      ]) := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .subWithOverflow w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  have hBits : truncateBits w
        (bvOfInt 128 (Int.ofNat x.toNat - Int.ofNat y.toNat)) =
      bvZeroExtend 128 (x - y) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [bvTruncMod_sub, toNat_truncateBits_bvOfInt_ofNat,
      toNat_truncateBits_bvOfInt_ofNat,
      nat_mod_eq_of_lt (bitVec_toNat_lt_pow x),
      nat_mod_eq_of_lt (bitVec_toNat_lt_pow y), toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_sub]
  exact (if_bool_false (Bool.and_false _)).trans
    ((congrArg (fun f => Except.ok (Val.tuple [Val.scalar ⟨w, false, _⟩,
      Val.bool f])) (unsigned_sub_overflow_flag_eq w x y)).trans
    (congrArg (fun b => Except.ok (Val.tuple [Val.scalar ⟨w, false, b⟩,
      Val.bool _])) hBits))

/-- Unsigned `evalBinOp .subUnchecked` succeeds with `x - y` iff
`y.toNat ≤ x.toNat` and faults with `.undefined` otherwise. -/
theorem evalBinOp_subUnchecked_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .subUnchecked (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      if y.toNat ≤ x.toNat then
        .ok (.scalar (bvToScalar w false (x - y)))
      else
        .error .undefined := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  change evalArithOp .subUnchecked w false
    (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar w false y)) = _
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  have hF := (Bool.and_true _).trans (unsigned_sub_overflow_flag_eq w x y)
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl hLt =>
    exact (if_bool_true (hF.trans (decide_eq_true hLt))).trans
      (ite_false_of (Nat.not_le_of_gt hLt)).symm
  | inr hGe =>
    have hBits : truncateBits w
          (bvOfInt 128 (Int.ofNat x.toNat - Int.ofNat y.toNat)) =
        bvZeroExtend 128 (x - y) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      have hw : 8 * w.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 w
      rw [bvTruncMod_sub, toNat_truncateBits_bvOfInt_ofNat,
        toNat_truncateBits_bvOfInt_ofNat,
        nat_mod_eq_of_lt (bitVec_toNat_lt_pow x),
        nat_mod_eq_of_lt (bitVec_toNat_lt_pow y), toNat_bvZeroExtend_of_le hw,
        Anneal.BitVec.toNat_sub]
    exact (if_bool_false
        (hF.trans (decide_eq_false (Nat.not_lt_of_ge hGe)))).trans
      ((congrArg (fun b => Except.ok (Val.scalar ⟨w, false, b⟩)) hBits).trans
        (ite_true_of hGe).symm)

/-- Unsigned `evalBinOp .lt` decides `x.toNat < y.toNat`. -/
theorem evalBinOp_lt_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .lt (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.bool (decide (x.toNat < y.toNat))) := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl h =>
    rw [decide_eq_true h, decide_eq_true (int_ofNat_lt_iff.mpr h)]
  | inr h =>
    rw [decide_eq_false (Nat.not_lt_of_ge h),
      decide_eq_false (fun hlt => Nat.not_lt_of_ge h (int_ofNat_lt_iff.mp hlt))]

/-- Unsigned `evalBinOp .le` decides `x.toNat ≤ y.toNat`. -/
theorem evalBinOp_le_unsigned_eq (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .le (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.bool (decide (x.toNat ≤ y.toNat))) := by
  refine (if_bool_false (evalBinOp_header_eq w false)).trans ?_
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq]
  cases Nat.lt_or_ge y.toNat x.toNat with
  | inl h =>
    have hN : ¬ (x.toNat ≤ y.toNat) := Nat.not_le_of_gt h
    rw [decide_eq_false hN,
      decide_eq_false (fun hle => hN (int_ofNat_le_iff.mp hle))]
  | inr h =>
    rw [decide_eq_true h, decide_eq_true (int_ofNat_le_iff.mpr h)]

/-- `evalBinOp .eq` decides bitvector equality `x = y` across both signedness
modes. -/
theorem evalBinOp_eq_eq (w : IntWidth) (s : Bool)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .eq (.scalar (bvToScalar w s x))
        (.scalar (bvToScalar w s y)) =
      .ok (.bool (decide (x = y))) := by
  refine (if_bool_false (evalBinOp_header_eq w s)).trans ?_
  cases Nat.decEq x.toNat y.toNat with
  | isTrue hEq =>
    have hBv : x = y := Anneal.BitVec.eq_of_toNat_eq hEq
    subst hBv
    have hb : (decodeScalar (bvToScalar w s x) ==
        decodeScalar (bvToScalar w s x)) = true := beq_self_eq_true _
    rw [hb, decide_eq_true rfl]
  | isFalse hNe =>
    have hBvNe : x ≠ y := fun h => hNe (congrArg BitVec.toNat h)
    have hDecNe : decodeScalar (bvToScalar w s x) ≠
        decodeScalar (bvToScalar w s y) :=
      fun h => hBvNe ((decodeScalar_eq_iff w s x y).mp h)
    have hb : (decodeScalar (bvToScalar w s x) ==
        decodeScalar (bvToScalar w s y)) = false := by
      cases hc : decodeScalar (bvToScalar w s x) ==
          decodeScalar (bvToScalar w s y) with
      | false => rfl
      | true => exact False.elim (hDecNe (of_decide_eq_true hc))
    rw [hb, decide_eq_false hBvNe]

/-- Signed `evalBinOp .lt` computes
`decide (Anneal.BitVecArith.signedKey x < Anneal.BitVecArith.signedKey y)`. -/
theorem evalBinOp_lt_signed_eq_decide (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .lt (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.bool (decide
        (Anneal.BitVecArith.signedKey x < Anneal.BitVecArith.signedKey y))) := by
  refine (if_bool_false (evalBinOp_header_eq w true)).trans ?_
  cases h : decide (decodeScalar (bvToScalar w true x) <
      decodeScalar (bvToScalar w true y)) with
  | true =>
    have hLt : Anneal.BitVecArith.signedKey x <
        Anneal.BitVecArith.signedKey y :=
      (decodeScalar_lt_iff_slt x y).mp (of_decide_eq_true h)
    rw [decide_eq_true hLt]
  | false =>
    have hNot : ¬ (Anneal.BitVecArith.signedKey x <
        Anneal.BitVecArith.signedKey y) :=
      fun hs => of_decide_eq_false h ((decodeScalar_lt_iff_slt x y).mpr hs)
    rw [decide_eq_false hNot]

/-- Signed `evalBinOp .lt` agrees with `Anneal.BitVecArith.slt x y`. -/
theorem evalBinOp_lt_signed_eq_slt (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ b : Bool,
      evalBinOp .lt (.scalar (bvToScalar w true x))
          (.scalar (bvToScalar w true y)) = .ok (.bool b) ∧
      (b = true ↔ Anneal.BitVecArith.slt x y) := by
  refine ⟨decide (Anneal.BitVecArith.signedKey x <
      Anneal.BitVecArith.signedKey y), evalBinOp_lt_signed_eq_decide w x y, ?_⟩
  exact ⟨fun h => @of_decide_eq_true
      (Anneal.BitVecArith.signedKey x < Anneal.BitVecArith.signedKey y) _ h,
    fun h => @decide_eq_true
      (Anneal.BitVecArith.signedKey x < Anneal.BitVecArith.signedKey y) _ h⟩

/-- Signed `evalBinOp .le` computes
`decide (Anneal.BitVecArith.signedKey x ≤ Anneal.BitVecArith.signedKey y)`. -/
theorem evalBinOp_le_signed_eq_decide (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    evalBinOp .le (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.bool (decide
        (Anneal.BitVecArith.signedKey x ≤ Anneal.BitVecArith.signedKey y))) := by
  refine (if_bool_false (evalBinOp_header_eq w true)).trans ?_
  cases h : decide (decodeScalar (bvToScalar w true x) ≤
      decodeScalar (bvToScalar w true y)) with
  | true =>
    have hLe : Anneal.BitVecArith.signedKey x ≤
        Anneal.BitVecArith.signedKey y :=
      (decodeScalar_le_iff_sle x y).mp (of_decide_eq_true h)
    rw [decide_eq_true hLe]
  | false =>
    have hNot : ¬ (Anneal.BitVecArith.signedKey x ≤
        Anneal.BitVecArith.signedKey y) :=
      fun hs => of_decide_eq_false h ((decodeScalar_le_iff_sle x y).mpr hs)
    rw [decide_eq_false hNot]

/-- Signed `evalBinOp .le` agrees with `Anneal.BitVecArith.sle x y`. -/
theorem evalBinOp_le_signed_eq_sle (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ b : Bool,
      evalBinOp .le (.scalar (bvToScalar w true x))
          (.scalar (bvToScalar w true y)) = .ok (.bool b) ∧
      (b = true ↔ Anneal.BitVecArith.sle x y) := by
  refine ⟨decide (Anneal.BitVecArith.signedKey x ≤
      Anneal.BitVecArith.signedKey y), evalBinOp_le_signed_eq_decide w x y, ?_⟩
  exact ⟨fun h => @of_decide_eq_true
      (Anneal.BitVecArith.signedKey x ≤ Anneal.BitVecArith.signedKey y) _ h,
    fun h => @decide_eq_true
      (Anneal.BitVecArith.signedKey x ≤ Anneal.BitVecArith.signedKey y) _ h⟩

private theorem intEmod_ofNat (a b : Nat) :
    intEmod (Int.ofNat a) (Int.ofNat b) = Int.ofNat (Nat.mod a b) := rfl

private theorem intShiftLeft_ofNat (a b : Nat) :
    intShiftLeft (Int.ofNat a) b = Int.ofNat (Nat.shiftLeft a b) := rfl

private theorem intShiftRight_ofNat (a b : Nat) :
    intShiftRight (Int.ofNat a) b = Int.ofNat (Nat.shiftRight a b) := rfl

/-- Unsigned `evalBinOp .shl` masks shift amount modulo `8 * w.byteSize` and
computes `Anneal.BitVec.shl`. -/
theorem evalBinOp_shl_unsigned_eq_shl (w wR : IntWidth)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shl (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar wR false y)) =
      .ok (.scalar (bvToScalar w false
        (Anneal.BitVec.shl x (Nat.mod y.toNat (8 * w.byteSize))))) := by
  change evalShiftOp .shl w false (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar wR false y)) = _
  unfold evalShiftOp
  dsimp only
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq,
    intEmod_ofNat]
  dsimp only [Int.toNat]
  rw [intShiftLeft_ofNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w false
    (Int.ofNat (Nat.shiftLeft x.toNat (Nat.mod y.toNat w.bitWidth)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shl.isUnchecked = false := rfl
  rw [hU, Bool.and_false, if_false_eq]
  have hBits : truncateBits w (bvOfInt 128
        (Int.ofNat (Nat.shiftLeft x.toNat (Nat.mod y.toNat w.bitWidth)))) =
      bvZeroExtend 128
        (Anneal.BitVec.shl x (Nat.mod y.toNat (8 * w.byteSize))) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits_bvOfInt_ofNat, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_shl, intWidth_bitWidth_eq_eight_mul]
  rw [hBits]
  rfl

/-- Unsigned `evalBinOp .shr` masks shift amount modulo `8 * w.byteSize` and
computes `Anneal.BitVec.ushr`. -/
theorem evalBinOp_shr_unsigned_eq_ushr (w wR : IntWidth)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shr (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar wR false y)) =
      .ok (.scalar (bvToScalar w false
        (Anneal.BitVec.ushr x (Nat.mod y.toNat (8 * w.byteSize))))) := by
  change evalShiftOp .shr w false (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar wR false y)) = _
  unfold evalShiftOp
  dsimp only
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq,
    intEmod_ofNat]
  dsimp only [Int.toNat]
  rw [intShiftRight_ofNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w false
    (Int.ofNat (Nat.shiftRight x.toNat (Nat.mod y.toNat w.bitWidth)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shr.isUnchecked = false := rfl
  rw [hU, Bool.and_false, if_false_eq]
  have hBits : truncateBits w (bvOfInt 128
        (Int.ofNat (Nat.shiftRight x.toNat (Nat.mod y.toNat w.bitWidth)))) =
      bvZeroExtend 128
        (Anneal.BitVec.ushr x (Nat.mod y.toNat (8 * w.byteSize))) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_truncateBits_bvOfInt_ofNat, toNat_bvZeroExtend_of_le hw,
      Anneal.BitVec.toNat_ushr, intWidth_bitWidth_eq_eight_mul]
    exact nat_mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)
  rw [hBits]
  rfl

private theorem truncate_not_ushr_not_eq_ashr {w : IntWidth}
    {x : BitVec (8 * w.byteSize)} (hm : Anneal.BitVecArith.msb x = true)
    (k : Nat) :
    (truncateBits w (bvOfInt 128 (Int.negSucc
        (Nat.shiftRight (Nat.pow 2 (8 * w.byteSize) - 1 - x.toNat) k)))).toNat =
      (Anneal.BitVecArith.ashr x k).toNat := by
  let W := 8 * w.byteSize
  have hNotEq : Nat.pow 2 W - 1 - x.toNat = (Anneal.BitVec.not x).toNat :=
    (Anneal.BitVecArith.toNat_not_eq_sub x).symm
  have hUshrLt :
      (Anneal.BitVec.ushr (Anneal.BitVec.not x) k).toNat < Nat.pow 2 W :=
    (Anneal.BitVec.ushr (Anneal.BitVec.not x) k).isLt
  rw [toNat_truncateBits_bvOfInt_negSucc, hNotEq]
  change Nat.pow 2 W - 1 -
      Nat.mod (Anneal.BitVec.ushr (Anneal.BitVec.not x) k).toNat (Nat.pow 2 W) =
    (Anneal.BitVecArith.ashr x k).toNat
  rw [nat_mod_eq_of_lt hUshrLt, ← Anneal.BitVecArith.toNat_not_eq_sub]
  apply congrArg BitVec.toNat
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Anneal.BitVec.getLsbD_not_of_lt _ hi, Anneal.BitVec.getLsbD_ushr,
    Anneal.BitVecArith.getLsbD_ashr, decide_eq_true hi, Bool.true_and]
  cases Nat.lt_or_ge (i + k) W with
  | inl hlt =>
    rw [ite_true_of hlt, Anneal.BitVec.getLsbD_not_of_lt _ hlt]
    cases Anneal.BitVec.getLsbD x (i + k) <;> rfl
  | inr hge =>
    rw [ite_false_of (Nat.not_lt_of_ge hge),
      Anneal.BitVec.getLsbD_ge _ hge, hm]
    rfl

/-- Signed `evalBinOp .shr` with unsigned RHS computes
`Anneal.BitVecArith.ashr x (y.toNat % (8 * w.byteSize))`. -/
theorem evalBinOp_shr_signed_eq_ashr (w wR : IntWidth)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shr (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar wR false y)) =
      .ok (.scalar (bvToScalar w true
        (Anneal.BitVecArith.ashr x (Nat.mod y.toNat (8 * w.byteSize))))) := by
  change evalShiftOp .shr w true (decodeScalar (bvToScalar w true x))
    (decodeScalar (bvToScalar wR false y)) = _
  unfold evalShiftOp
  dsimp only
  rw [decodeScalar_unsigned_eq, intEmod_ofNat]
  dsimp only [Int.toNat]
  let k := Nat.mod y.toNat w.bitWidth
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w true
    (intShiftRight (decodeScalar (bvToScalar w true x)) k)
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shr.isUnchecked = false := rfl
  rw [hU, Bool.and_false, if_false_eq]
  have hBits : truncateBits w
        (bvOfInt 128 (intShiftRight (decodeScalar (bvToScalar w true x)) k)) =
      bvZeroExtend 128
        (Anneal.BitVecArith.ashr x (Nat.mod y.toNat (8 * w.byteSize))) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    have hk : k = Nat.mod y.toNat (8 * w.byteSize) := by
      dsimp only [k]
      rw [intWidth_bitWidth_eq_eight_mul]
    rw [toNat_bvZeroExtend_of_le hw, hk]
    cases hm : Anneal.BitVecArith.msb x with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm, intShiftRight_ofNat,
        toNat_truncateBits_bvOfInt_ofNat,
        Anneal.BitVecArith.ashr_of_msb_false _ hm,
        Anneal.BitVec.toNat_ushr]
      exact nat_mod_eq_of_lt
        (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)
    | true =>
      rw [decodeScalar_signed_of_msb_true hm, intShiftRight]
      exact truncate_not_ushr_not_eq_ashr hm _
  change Except.ok (Val.scalar ⟨w, true, truncateBits w
      (bvOfInt 128 (intShiftRight (decodeScalar (bvToScalar w true x)) k))⟩) = _
  rw [hBits]
  rfl

/-- Unsigned unchecked left shifts fault on `y.toNat ≥ 8 * w.byteSize` and
agree with `shl` when `y.toNat < 8 * w.byteSize`. -/
theorem evalBinOp_shlUnchecked_unsigned_eq (w wR : IntWidth)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shlUnchecked (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar wR false y)) =
      if y.toNat < 8 * w.byteSize then
        .ok (.scalar (bvToScalar w false (Anneal.BitVec.shl x y.toNat)))
      else
        .error .undefined := by
  change evalShiftOp .shlUnchecked w false (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar wR false y)) = _
  unfold evalShiftOp
  dsimp only
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq,
    intEmod_ofNat]
  dsimp only [Int.toNat]
  rw [intShiftLeft_ofNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w false
    (Int.ofNat (Nat.shiftLeft x.toNat (Nat.mod y.toNat w.bitWidth)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shlUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true]
  cases Nat.lt_or_ge y.toNat (8 * w.byteSize) with
  | inl hLt =>
    have hLtW : y.toNat < w.bitWidth := by
      rw [intWidth_bitWidth_eq_eight_mul]
      exact hLt
    have hModEq : Nat.mod y.toNat w.bitWidth = y.toNat :=
      nat_mod_eq_of_lt hLtW
    have hOvf : (Int.ofNat (Nat.mod y.toNat w.bitWidth) != Int.ofNat y.toNat) =
        false := by
      change (!(Int.ofNat (Nat.mod y.toNat w.bitWidth) ==
          Int.ofNat y.toNat)) = false
      rw [hModEq, beq_self_eq_true]
      rfl
    rw [ite_true_of hLt, hOvf, if_false_eq]
    have hBits : truncateBits w (bvOfInt 128
          (Int.ofNat (Nat.shiftLeft x.toNat (Nat.mod y.toNat w.bitWidth)))) =
        bvZeroExtend 128 (Anneal.BitVec.shl x y.toNat) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      have hw : 8 * w.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 w
      rw [hModEq, toNat_truncateBits_bvOfInt_ofNat,
        toNat_bvZeroExtend_of_le hw, Anneal.BitVec.toNat_shl]
    change Except.ok (Val.scalar ⟨w, false, truncateBits w (bvOfInt 128
        (Int.ofNat (Nat.shiftLeft x.toNat (Nat.mod y.toNat w.bitWidth))))⟩) = _
    rw [hBits]
    rfl
  | inr hGe =>
    have hGeW : w.bitWidth ≤ y.toNat := by
      rw [intWidth_bitWidth_eq_eight_mul]
      exact hGe
    have hModLt : Nat.mod y.toNat w.bitWidth < y.toNat :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (intWidth_bitWidth_pos w)) hGeW
    have hNe : Int.ofNat (Nat.mod y.toNat w.bitWidth) ≠ Int.ofNat y.toNat :=
      fun h => Nat.ne_of_lt hModLt (Int.ofNat.inj h)
    have hOvf : (Int.ofNat (Nat.mod y.toNat w.bitWidth) != Int.ofNat y.toNat) =
        true := bne_iff_ne.mpr hNe
    rw [ite_false_of (Nat.not_lt_of_ge hGe), hOvf, if_true_eq]

/-- Unsigned unchecked right shifts fault on `y.toNat ≥ 8 * w.byteSize` and
agree with `ushr` when `y.toNat < 8 * w.byteSize`. -/
theorem evalBinOp_shrUnchecked_unsigned_eq (w wR : IntWidth)
    (x : BitVec (8 * w.byteSize)) (y : BitVec (8 * wR.byteSize)) :
    evalBinOp .shrUnchecked (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar wR false y)) =
      if y.toNat < 8 * w.byteSize then
        .ok (.scalar (bvToScalar w false (Anneal.BitVec.ushr x y.toNat)))
      else
        .error .undefined := by
  change evalShiftOp .shrUnchecked w false (decodeScalar (bvToScalar w false x))
    (decodeScalar (bvToScalar wR false y)) = _
  unfold evalShiftOp
  dsimp only
  rw [decodeScalar_unsigned_eq, decodeScalar_unsigned_eq,
    intEmod_ofNat]
  dsimp only [Int.toNat]
  rw [intShiftRight_ofNat]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w false
    (Int.ofNat (Nat.shiftRight x.toNat (Nat.mod y.toNat w.bitWidth)))
  rw [hTrunc]
  dsimp only
  have hU : BinOp.shrUnchecked.isUnchecked = true := rfl
  rw [hU, Bool.and_true]
  cases Nat.lt_or_ge y.toNat (8 * w.byteSize) with
  | inl hLt =>
    have hLtW : y.toNat < w.bitWidth := by
      rw [intWidth_bitWidth_eq_eight_mul]
      exact hLt
    have hModEq : Nat.mod y.toNat w.bitWidth = y.toNat :=
      nat_mod_eq_of_lt hLtW
    have hOvf : (Int.ofNat (Nat.mod y.toNat w.bitWidth) != Int.ofNat y.toNat) =
        false := by
      change (!(Int.ofNat (Nat.mod y.toNat w.bitWidth) ==
          Int.ofNat y.toNat)) = false
      rw [hModEq, beq_self_eq_true]
      rfl
    rw [ite_true_of hLt, hOvf, if_false_eq]
    have hBits : truncateBits w (bvOfInt 128
          (Int.ofNat (Nat.shiftRight x.toNat (Nat.mod y.toNat w.bitWidth)))) =
        bvZeroExtend 128 (Anneal.BitVec.ushr x y.toNat) := by
      apply Anneal.BitVec.eq_of_toNat_eq
      have hw : 8 * w.byteSize ≤ 128 := by
        rw [← intWidth_bitWidth_eq_eight_mul]
        exact intWidth_bitWidth_le_128 w
      rw [hModEq, toNat_truncateBits_bvOfInt_ofNat,
        toNat_bvZeroExtend_of_le hw, Anneal.BitVec.toNat_ushr]
      exact nat_mod_eq_of_lt
        (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)
    change Except.ok (Val.scalar ⟨w, false, truncateBits w (bvOfInt 128
        (Int.ofNat (Nat.shiftRight x.toNat (Nat.mod y.toNat w.bitWidth))))⟩) = _
    rw [hBits]
    rfl
  | inr hGe =>
    have hGeW : w.bitWidth ≤ y.toNat := by
      rw [intWidth_bitWidth_eq_eight_mul]
      exact hGe
    have hModLt : Nat.mod y.toNat w.bitWidth < y.toNat :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (intWidth_bitWidth_pos w)) hGeW
    have hNe : Int.ofNat (Nat.mod y.toNat w.bitWidth) ≠ Int.ofNat y.toNat :=
      fun h => Nat.ne_of_lt hModLt (Int.ofNat.inj h)
    have hOvf : (Int.ofNat (Nat.mod y.toNat w.bitWidth) != Int.ofNat y.toNat) =
        true := bne_iff_ne.mpr hNe
    rw [ite_false_of (Nat.not_lt_of_ge hGe), hOvf, if_true_eq]

/-- `evalUnOp .not` on both unsigned and signed scalars computes
`Anneal.BitVec.not`. -/
theorem evalUnOp_not_eq_not (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    evalUnOp .not (.scalar (bvToScalar w s x)) =
      .ok (.scalar (bvToScalar w s (Anneal.BitVec.not x))) := by
  unfold evalUnOp
  dsimp only
  rw [bvToScalar_width, bvToScalar_signed]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w s
    (intNot (decodeScalar (bvToScalar w s x)))
  rw [hTrunc]
  dsimp only
  have hBits : truncateBits w
        (bvOfInt 128 (intNot (decodeScalar (bvToScalar w s x)))) =
      bvZeroExtend 128 (Anneal.BitVec.not x) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    rw [toNat_bvZeroExtend_of_le hw, Anneal.BitVecArith.toNat_not_eq_sub]
    cases s with
    | false =>
      rw [decodeScalar_unsigned_eq, intNot, toNat_truncateBits_bvOfInt_negSucc,
        nat_mod_eq_of_lt (bitVec_toNat_lt_pow x)]
    | true =>
      cases hm : Anneal.BitVecArith.msb x with
      | false =>
        rw [decodeScalar_signed_of_msb_false hm, intNot,
          toNat_truncateBits_bvOfInt_negSucc,
          nat_mod_eq_of_lt (bitVec_toNat_lt_pow x)]
      | true =>
        rw [decodeScalar_signed_of_msb_true hm, intNot,
          toNat_truncateBits_bvOfInt_ofNat]
        exact nat_mod_eq_of_lt
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
            (Nat.sub_lt (nat_two_pow_pos _) Nat.one_pos))
  change Except.ok (Val.scalar ⟨w, s, truncateBits w
      (bvOfInt 128 (intNot (decodeScalar (bvToScalar w s x))))⟩) = _
  rw [hBits]
  rfl

/-- `evalUnOp .neg` on signed scalars computes `Anneal.BitVecArith.neg`. See
`evalUnOp_neg_unsigned_unsupported` for unsigned scalars. -/
theorem evalUnOp_neg_signed_eq_neg (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    evalUnOp .neg (.scalar (bvToScalar w true x)) =
      .ok (.scalar (bvToScalar w true (Anneal.BitVecArith.neg x))) := by
  unfold evalUnOp
  dsimp only
  rw [bvToScalar_width, bvToScalar_signed, if_true_eq]
  let ⟨lossy, hTrunc⟩ := truncateScalar_val_eq w true
    (Neg.neg (decodeScalar (bvToScalar w true x)))
  rw [hTrunc]
  dsimp only
  have hBits : truncateBits w
        (bvOfInt 128 (Neg.neg (decodeScalar (bvToScalar w true x)))) =
      bvZeroExtend 128 (Anneal.BitVecArith.neg x) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw : 8 * w.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w
    change (truncateBits w
        (bvOfInt 128 (Int.neg (decodeScalar (bvToScalar w true x))))).toNat = _
    rw [bvTruncMod_neg, truncateBits_bvOfInt_decode,
      toNat_bvZeroExtend_of_le hw, Anneal.BitVecArith.toNat_neg]
  change Except.ok (Val.scalar ⟨w, true, truncateBits w
      (bvOfInt 128 (Neg.neg (decodeScalar (bvToScalar w true x))))⟩) = _
  rw [hBits]
  rfl

/-- `evalUnOp .neg` rejects unsigned scalars with `.error .unsupported`. -/
theorem evalUnOp_neg_unsigned_unsupported (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    evalUnOp .neg (.scalar (bvToScalar w false x)) = .error .unsupported :=
  rfl

/-- `evalIntToIntCast` from an unsigned scalar computes
`Anneal.BitVec.setWidth`. -/
theorem evalIntToIntCast_unsigned_eq_setWidth (w₁ w₂ : IntWidth) (s₂ : Bool)
    (x : BitVec (8 * w₁.byteSize)) :
    evalIntToIntCast (.scalar (bvToScalar w₁ false x)) (.int w₂ s₂) =
      .ok (.scalar (bvToScalar w₂ s₂
        (Anneal.BitVec.setWidth (8 * w₂.byteSize) x))) := by
  unfold evalIntToIntCast intLikeBits
  dsimp only
  have hw1 : 8 * w₁.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w₁
  rw [bvToScalar_width, bvToScalar_signed, if_false_eq]
  dsimp only [bvToScalar]
  rw [truncateBits_bvZeroExtend, toNat_bvZeroExtend_of_le hw1 x]
  have hBits : truncateBits w₂ (BitVec.ofNat 128 x.toNat) =
      bvZeroExtend 128 (Anneal.BitVec.setWidth (8 * w₂.byteSize) x) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw2 : 8 * w₂.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w₂
    have hx128 : x.toNat < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by decide : 0 < 2) hw1)
    rw [toNat_truncateBits, intWidthModulus_eq_pow_eight,
      Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hx128,
      toNat_bvZeroExtend_of_le hw2, Anneal.BitVec.toNat_setWidth]
  change Except.ok (Val.scalar ⟨w₂, s₂, truncateBits w₂ (BitVec.ofNat 128 x.toNat)⟩) = _
  rw [hBits]

/-- `evalIntToIntCast` from a signed scalar computes
`Anneal.BitVecArith.signExtend`. -/
theorem evalIntToIntCast_signed_eq_signExtend (w₁ w₂ : IntWidth) (s₂ : Bool)
    (x : BitVec (8 * w₁.byteSize)) :
    evalIntToIntCast (.scalar (bvToScalar w₁ true x)) (.int w₂ s₂) =
      .ok (.scalar (bvToScalar w₂ s₂
        (Anneal.BitVecArith.signExtend (8 * w₂.byteSize) x))) := by
  unfold evalIntToIntCast intLikeBits
  dsimp only
  rw [bvToScalar_width, bvToScalar_signed, if_true_eq]
  let bits := (bvOfInt 128 (decodeScalar (bvToScalar w₁ true x))).toNat
  have hBitsLt128 : bits < Nat.pow 2 128 :=
    (bvOfInt 128 (decodeScalar (bvToScalar w₁ true x))).isLt
  have hBits : truncateBits w₂ (BitVec.ofNat 128 bits) =
      bvZeroExtend 128 (Anneal.BitVecArith.signExtend (8 * w₂.byteSize) x) := by
    apply Anneal.BitVec.eq_of_toNat_eq
    have hw1 : 8 * w₁.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w₁
    have hw2 : 8 * w₂.byteSize ≤ 128 := by
      rw [← intWidth_bitWidth_eq_eight_mul]
      exact intWidth_bitWidth_le_128 w₂
    rw [toNat_truncateBits, Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt hBitsLt128, toNat_bvZeroExtend_of_le hw2]
    change Nat.mod (bvOfInt 128 (decodeScalar (bvToScalar w₁ true x))).toNat
        (intWidthModulus w₂) = _
    rw [← toNat_truncateBits]
    let W₁ := 8 * w₁.byteSize
    let W₂ := 8 * w₂.byteSize
    cases hm : Anneal.BitVecArith.msb x with
    | false =>
      rw [decodeScalar_signed_of_msb_false hm, toNat_truncateBits_bvOfInt_ofNat,
        Anneal.BitVecArith.signExtend_of_msb_false W₂ hm,
        Anneal.BitVec.toNat_setWidth]
    | true =>
      rw [decodeScalar_signed_of_msb_true hm, toNat_truncateBits_bvOfInt_negSucc]
      cases Nat.lt_or_ge W₁ W₂ with
      | inr hLe =>
        have hSign :
            (Anneal.BitVecArith.signExtend W₂ x).toNat =
              Nat.mod x.toNat (Nat.pow 2 W₂) := by
          have hBv : Anneal.BitVecArith.signExtend W₂ x =
              BitVec.ofNat W₂ x.toNat := by
            apply Anneal.BitVec.eq_of_getLsbD_eq
            intro i hi
            rw [Anneal.BitVecArith.getLsbD_signExtend, Anneal.BitVec.getLsbD_ofNat,
              decide_eq_true hi, Bool.true_and,
              ite_true_of (Nat.lt_of_lt_of_le hi hLe)]
            rfl
          rw [hBv, Anneal.BitVec.toNat_ofNat]
        rw [hSign]
        -- Mod of (2^W1 - 1 - x) mod 2^W2 equals 2^W2 - 1 - (x mod 2^W2).
        have hPow1 : Nat.pow 2 W₁ =
            Nat.pow 2 W₂ * Nat.pow 2 (W₁ - W₂) := by
          have hEq : W₁ = W₂ + (W₁ - W₂) := (Nat.add_sub_of_le hLe).symm
          have hP := congrArg (Nat.pow 2) hEq
          rw [nat_pow_add] at hP
          exact hP
        have hrLt : Nat.mod x.toNat (Nat.pow 2 W₂) < Nat.pow 2 W₂ :=
          Nat.mod_lt x.toNat (nat_two_pow_pos W₂)
        have hrLe : Nat.mod x.toNat (Nat.pow 2 W₂) ≤ Nat.pow 2 W₂ - 1 :=
          Nat.le_sub_one_of_lt hrLt
        have hM1 : Nat.mod (Nat.pow 2 W₁ - 1 - x.toNat) (Nat.pow 2 W₂) =
            Nat.pow 2 W₂ - 1 - Nat.mod x.toNat (Nat.pow 2 W₂) := by
          let P := Nat.pow 2 W₂
          have hPpos : 0 < P := nat_two_pow_pos W₂
          have hxLt : x.toNat < Nat.pow 2 W₁ := x.isLt
          have hrLeP : Nat.mod x.toNat P ≤ P - 1 := hrLe
          have hxDec : x.toNat = P * Nat.div x.toNat P + Nat.mod x.toNat P :=
            (nat_div_add_mod x.toNat P).symm
          have hqLt : Nat.div x.toNat P < Nat.pow 2 (W₁ - W₂) := by
            have h1 : P * Nat.div x.toNat P < P * Nat.pow 2 (W₁ - W₂) := by
              have hLe1 : P * Nat.div x.toNat P ≤ P * Nat.div x.toNat P +
                  Nat.mod x.toNat P := Nat.le_add_right _ _
              rw [← hxDec] at hLe1
              rw [← hPow1]
              exact Nat.lt_of_le_of_lt hLe1 hxLt
            cases Nat.lt_or_ge (Nat.div x.toNat P) (Nat.pow 2 (W₁ - W₂)) with
            | inl h => exact h
            | inr h =>
              exact False.elim (Nat.not_le_of_gt h1 (Nat.mul_le_mul_left P h))
          have hK1 : 1 ≤ Nat.pow 2 (W₁ - W₂) := nat_two_pow_pos (W₁ - W₂)
          have hqK1 : Nat.div x.toNat P ≤ Nat.pow 2 (W₁ - W₂) - 1 :=
            Nat.le_sub_one_of_lt hqLt
          have hSum : Nat.pow 2 W₁ - 1 =
              (P - 1 - Nat.mod x.toNat P +
                P * (Nat.pow 2 (W₁ - W₂) - 1 - Nat.div x.toNat P)) +
                x.toNat := by
            have hKeq : 1 + (Nat.pow 2 (W₁ - W₂) - 1 - Nat.div x.toNat P) +
                Nat.div x.toNat P = Nat.pow 2 (W₁ - W₂) := by
              rw [Nat.add_comm 1 _, Nat.add_assoc,
                Nat.add_comm 1 (Nat.div x.toNat P), ← Nat.add_assoc,
                Nat.sub_add_cancel hqK1, Nat.sub_add_cancel hK1]
            have hMul := congrArg (fun z => P * z) hKeq
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hMul
            have h1 : (P - 1 - Nat.mod x.toNat P) + Nat.mod x.toNat P = P - 1 :=
              Nat.sub_add_cancel hrLeP
            have hAlg1 : ∀ a b c d : Nat,
                a + d = P - 1 → P + b + c = Nat.pow 2 W₁ →
                ((a + b) + (c + d)) + 1 = Nat.pow 2 W₁ := by
              intro a b c d hA hM
              rw [Nat.add_comm c d, ← Nat.add_assoc (a + b) d c,
                Nat.add_assoc a b d, Nat.add_comm b d, ← Nat.add_assoc a d b, hA,
                Nat.add_comm ((P - 1 + b) + c) 1,
                ← Nat.add_assoc 1 (P - 1 + b) c, ← Nat.add_assoc 1 (P - 1) b,
                Nat.add_comm 1 (P - 1), Nat.sub_add_cancel hPpos, hM]
            have hFinalSum :
                ((P - 1 - Nat.mod x.toNat P +
                  P * (Nat.pow 2 (W₁ - W₂) - 1 - Nat.div x.toNat P)) +
                  x.toNat) + 1 = Nat.pow 2 W₁ := by
              have hS := hAlg1 (P - 1 - Nat.mod x.toNat P)
                (P * (Nat.pow 2 (W₁ - W₂) - 1 - Nat.div x.toNat P))
                (P * Nat.div x.toNat P) (Nat.mod x.toNat P)
                h1 (hMul.trans hPow1.symm)
              exact (congrArg (fun z =>
                ((P - 1 - Nat.mod x.toNat P +
                  P * (Nat.pow 2 (W₁ - W₂) - 1 - Nat.div x.toNat P)) + z) + 1)
                hxDec).trans hS
            have hPred := congrArg (fun z => z - 1) hFinalSum
            rw [Nat.add_sub_cancel] at hPred
            exact hPred.symm
          have hDiff : Nat.pow 2 W₁ - 1 - x.toNat =
              (P - 1 - Nat.mod x.toNat P) +
                P * (Nat.pow 2 (W₁ - W₂) - 1 - Nat.div x.toNat P) := by
            have h2 := congrArg (fun z => z - x.toNat) hSum
            rw [Nat.add_sub_cancel] at h2
            exact h2
          rw [hDiff, nat_add_mul_mod_self_left]
          exact nat_mod_eq_of_lt
            (Nat.lt_of_le_of_lt (Nat.sub_le (P - 1) (Nat.mod x.toNat P))
              (Nat.sub_lt hPpos Nat.one_pos))
        rw [hM1, nat_sub_sub_cancel_of_le hrLe]
      | inl hGt =>
        have hWLe : W₁ ≤ W₂ := Nat.le_of_lt hGt
        have hPowLe : Nat.pow 2 W₁ ≤ Nat.pow 2 W₂ :=
          Nat.pow_le_pow_right (by decide : 0 < 2) hWLe
        have hDLt : Nat.pow 2 W₁ - 1 - x.toNat < Nat.pow 2 W₂ :=
          Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
              (Nat.sub_lt (nat_two_pow_pos W₁) Nat.one_pos))
            hPowLe
        rw [nat_mod_eq_of_lt hDLt]
        have hNotSign :
            Anneal.BitVec.not (Anneal.BitVecArith.signExtend W₂ x) =
              Anneal.BitVec.setWidth W₂ (Anneal.BitVec.not x) := by
          apply Anneal.BitVec.eq_of_getLsbD_eq
          intro i hi
          rw [Anneal.BitVec.getLsbD_not_of_lt _ hi,
            Anneal.BitVecArith.getLsbD_signExtend,
            Anneal.BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
          cases Nat.lt_or_ge i W₁ with
          | inl hlt =>
            rw [ite_true_of hlt, Anneal.BitVec.getLsbD_not_of_lt _ hlt,
              Bool.true_and]
          | inr hge =>
            rw [ite_false_of (Nat.not_lt_of_ge hge), hm, Bool.not_true,
              Anneal.BitVec.getLsbD_ge _ hge, Bool.true_and]
        have hToNat := congrArg BitVec.toNat hNotSign
        rw [Anneal.BitVecArith.toNat_not_eq_sub, Anneal.BitVec.toNat_setWidth,
          Anneal.BitVecArith.toNat_not_eq_sub, nat_mod_eq_of_lt hDLt] at hToNat
        have hInv := congrArg (fun z => Nat.pow 2 W₂ - 1 - z) hToNat.symm
        rw [nat_sub_sub_cancel_of_le (Nat.le_sub_one_of_lt
          (bitVec_toNat_lt_pow (Anneal.BitVecArith.signExtend W₂ x)))] at hInv
        exact hInv
  change Except.ok (Val.scalar ⟨w₂, s₂, truncateBits w₂ (BitVec.ofNat 128 bits)⟩) = _
  rw [hBits]
  rfl

/-! ### Tnum Adequacy Lift for MIR Bitwise & Wrapping Addition -/

/-- `Anneal.BitVec.tnum_and_sound` lifted directly to operational
`Trusted.MirSemantics.evalBinOp .bitAnd` on `bvToScalar`. -/
theorem evalBinOp_bitAnd_tnum_sound {w : IntWidth} (s : Bool)
    {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec (8 * w.byteSize)}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂) :
    ∃ r : BitVec (8 * w.byteSize),
      evalBinOp .bitAnd (.scalar (bvToScalar w s x₁))
          (.scalar (bvToScalar w s x₂)) =
        .ok (.scalar (bvToScalar w s r)) ∧
      Anneal.BitVec.MaskEq
        (Anneal.BitVec.or
          (Anneal.BitVec.or (Anneal.BitVec.and m₁ m₂)
            (Anneal.BitVec.and m₁ v₂))
          (Anneal.BitVec.and v₁ m₂))
        r (Anneal.BitVec.and v₁ v₂) :=
  ⟨Anneal.BitVec.and x₁ x₂, evalBinOp_bitAnd_eq_and w s x₁ x₂,
    Anneal.BitVec.tnum_and_sound h₁ h₂⟩

/-- `Anneal.BitVecArith.tnum_add_sound_general` lifted directly to operational
`Trusted.MirSemantics.evalBinOp .add` on `bvToScalar`. -/
theorem evalBinOp_add_tnum_sound {w : IntWidth} (s : Bool)
    {m₁ m₂ x₁ x₂ v₁ v₂ : BitVec (8 * w.byteSize)}
    (h₁ : Anneal.BitVec.MaskEq m₁ x₁ v₁)
    (h₂ : Anneal.BitVec.MaskEq m₂ x₂ v₂) :
    ∃ r : BitVec (8 * w.byteSize),
      evalBinOp .add (.scalar (bvToScalar w s x₁))
          (.scalar (bvToScalar w s x₂)) =
        .ok (.scalar (bvToScalar w s r)) ∧
      let v₁' := Anneal.BitVec.and v₁ (Anneal.BitVec.not m₁)
      let v₂' := Anneal.BitVec.and v₂ (Anneal.BitVec.not m₂)
      let sm := m₁ + m₂
      let sv := v₁' + v₂'
      let sigma := sm + sv
      let chi := Anneal.BitVec.xor sigma sv
      let mu := Anneal.BitVec.or chi (Anneal.BitVec.or m₁ m₂)
      Anneal.BitVec.MaskEq mu r
        (Anneal.BitVec.and sv (Anneal.BitVec.not mu)) :=
  ⟨x₁ + x₂, evalBinOp_add_eq_add w s x₁ x₂,
    Anneal.BitVecArith.tnum_add_sound_general h₁ h₂⟩

/-! ## 4. Byte-Order Serialization & Chunking Adequacy -/

/-- Embed a `BitVec 8` byte as an initialized `Trusted.MirModel.AllocByte`
carrying optional provenance `prov`. -/
@[expose] def allocByteOfBv (prov : Option AllocId := none) (b : BitVec 8) :
    AllocByte :=
  .init (UInt8.ofBitVec b) prov

/-- Extract the `BitVec 8` payload of every initialized `AllocByte`, skipping
`.uninit` bytes. -/
@[expose] def extractInitBvBytes (bs : List AllocByte) : List (BitVec 8) :=
  bs.foldr
    (fun head acc =>
      match head with
      | .uninit => acc
      | .init b _ => b.toBitVec :: acc)
    []

/-- `allocByteOfBv` is injective in the `BitVec 8` payload. -/
theorem allocByteOfBv_injective {prov : Option AllocId} {a b : BitVec 8}
    (h : allocByteOfBv prov a = allocByteOfBv prov b) : a = b := by
  injection h with hU _
  exact congrArg UInt8.toBitVec hU

/-- Embedded byte lists are always fully initialized (`allBytesInit`). -/
theorem allBytesInit_map_allocByteOfBv (prov : Option AllocId) :
    ∀ bs : List (BitVec 8),
      allBytesInit (bs.map (allocByteOfBv prov)) = true
  | [] => rfl
  | _ :: rest => allBytesInit_map_allocByteOfBv prov rest

/-- Left inverse: `extractInitBvBytes` undoes `List.map (allocByteOfBv prov)`.
-/
theorem extractInitBvBytes_map_allocByteOfBv (prov : Option AllocId) :
    ∀ bs : List (BitVec 8),
      extractInitBvBytes (bs.map (allocByteOfBv prov)) = bs
  | [] => rfl
  | b :: rest =>
    congrArg (List.cons b) (extractInitBvBytes_map_allocByteOfBv prov rest)

private theorem allBytesInit_drop :
    ∀ (n : Nat) (bs : List AllocByte),
      allBytesInit bs = true → allBytesInit (bs.drop n) = true
  | 0, _, h => h
  | _ + 1, [], h => h
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init _ _ :: rest, h => allBytesInit_drop k rest h

private theorem list_length_map {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (list_length_map f rest)

private theorem list_length_append {α : Type} :
    ∀ xs ys : List α, (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | _ :: rest, ys => by
    rw [List.cons_append, List.length_cons, List.length_cons,
      list_length_append rest ys, Nat.succ_add]

private theorem list_append_nil {α : Type} :
    ∀ xs : List α, xs ++ [] = xs
  | [] => rfl
  | x :: rest => congrArg (List.cons x) (list_append_nil rest)

private theorem list_append_assoc {α : Type} :
    ∀ xs ys zs : List α, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | x :: rest, ys, zs =>
    congrArg (List.cons x) (list_append_assoc rest ys zs)

private theorem list_map_append {α β : Type} (f : α → β) :
    ∀ xs ys : List α, (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: rest, ys =>
    congrArg (List.cons (f x)) (list_map_append f rest ys)

private theorem list_reverse_append {α : Type} :
    ∀ xs ys : List α, (xs ++ ys).reverse = ys.reverse ++ xs.reverse
  | [], ys => (list_append_nil ys.reverse).symm
  | x :: rest, ys => by
    rw [List.cons_append, List.reverse_cons, list_reverse_append rest ys,
      List.reverse_cons, list_append_assoc]

private theorem list_map_reverse {α β : Type} (f : α → β) :
    ∀ xs : List α, xs.reverse.map f = (xs.map f).reverse
  | [] => rfl
  | x :: rest => by
    rw [List.reverse_cons, list_map_append, list_map_reverse f rest,
      List.map_cons, List.map_nil, List.map_cons, List.reverse_cons]

private theorem list_length_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), (xs.drop n).length = xs.length - n
  | 0, xs => (Nat.sub_zero xs.length).symm
  | n + 1, [] => (Nat.zero_sub (n + 1)).symm
  | n + 1, _ :: rest => by
    change (rest.drop n).length = rest.length + 1 - (n + 1)
    rw [list_length_drop n rest, Nat.succ_sub_succ_eq_sub]

private theorem length_extractInitBvBytes_le :
    ∀ bs : List AllocByte, (extractInitBvBytes bs).length ≤ bs.length
  | [] => Nat.le_refl 0
  | .uninit :: rest => Nat.le_succ_of_le (length_extractInitBvBytes_le rest)
  | .init _ _ :: rest => Nat.succ_le_succ (length_extractInitBvBytes_le rest)

/-- `extractInitBvBytes` preserves list length iff `allBytesInit bs = true`.
-/
theorem length_extractInitBvBytes_eq_iff :
    ∀ bs : List AllocByte,
      (extractInitBvBytes bs).length = bs.length ↔ allBytesInit bs = true
  | [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | .uninit :: rest => by
    have hle := length_extractInitBvBytes_le rest
    constructor
    · intro h
      have h' : (extractInitBvBytes rest).length = rest.length + 1 := h
      rw [h'] at hle
      exact False.elim (Nat.not_lt_of_ge hle (Nat.lt_succ_self _))
    · intro h
      cases h
  | .init _ _ :: rest => by
    have ih := length_extractInitBvBytes_eq_iff rest
    constructor
    · intro h
      have h' : (extractInitBvBytes rest).length + 1 = rest.length + 1 := h
      exact ih.mp (Nat.succ.inj h')
    · intro h
      change (extractInitBvBytes rest).length + 1 = rest.length + 1
      rw [ih.mpr h]

private theorem extractInitBvBytes_take :
    ∀ (n : Nat) (bs : List AllocByte),
      allBytesInit bs = true →
        extractInitBvBytes (bs.take n) = (extractInitBvBytes bs).take n
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init b _ :: rest, h =>
    congrArg (List.cons b.toBitVec) (extractInitBvBytes_take k rest h)

private theorem extractInitBvBytes_drop :
    ∀ (n : Nat) (bs : List AllocByte),
      allBytesInit bs = true →
        extractInitBvBytes (bs.drop n) = (extractInitBvBytes bs).drop n
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, .uninit :: _, h => nomatch h
  | k + 1, .init _ _ :: rest, h => extractInitBvBytes_drop k rest h

/-- On any fully initialized `AllocByte` list, `extractInitBvBytes` commutes
with `Anneal.ListChunks.chunksOf n` for every `n : Nat`. -/
theorem chunksOf_extractInitBvBytes (n : Nat) (bs : List AllocByte)
    (hinit : allBytesInit bs = true) :
    (Anneal.ListChunks.chunksOf n bs).map extractInitBvBytes =
      Anneal.ListChunks.chunksOf n (extractInitBvBytes bs) := by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    subst hn
    rfl
  | inr hn =>
    have haux : ∀ (fuel : Nat) (xs : List AllocByte),
        allBytesInit xs = true → xs.length ≤ fuel →
          (Anneal.ListChunks.chunksOfAux n fuel xs).map extractInitBvBytes =
            Anneal.ListChunks.chunksOfAux n fuel (extractInitBvBytes xs) := by
      intro fuel
      induction fuel with
      | zero =>
        intro xs _ _
        rfl
      | succ f ih =>
        intro xs hxi hle
        cases xs with
        | nil => rfl
        | cons b rest =>
          cases b with
          | uninit => nomatch hxi
          | init byte prov =>
            have hNotZ : (Nat.beq n 0) = false := by
              cases hn' : n with
              | zero =>
                rw [hn'] at hn
                exact False.elim (Nat.lt_irrefl 0 hn)
              | succ _ => rfl
            have hStep1 : Anneal.ListChunks.chunksOfAux n (f + 1)
                  (.init byte prov :: rest) =
                ((AllocByte.init byte prov :: rest).take n) ::
                  Anneal.ListChunks.chunksOfAux n f
                    ((AllocByte.init byte prov :: rest).drop n) := rfl
            have hStep2 : Anneal.ListChunks.chunksOfAux n (f + 1)
                  (extractInitBvBytes (.init byte prov :: rest)) =
                ((extractInitBvBytes (.init byte prov :: rest)).take n) ::
                  Anneal.ListChunks.chunksOfAux n f
                    ((extractInitBvBytes (.init byte prov :: rest)).drop n) := rfl
            rw [hStep1, List.map_cons, hStep2,
              extractInitBvBytes_take n _ hxi, ← extractInitBvBytes_drop n _ hxi]
            have hdrop_init : allBytesInit
                ((AllocByte.init byte prov :: rest).drop n) = true :=
              allBytesInit_drop n _ hxi
            have hdrop_le :
                ((AllocByte.init byte prov :: rest).drop n).length ≤ f := by
              rw [list_length_drop, List.length_cons]
              rw [List.length_cons] at hle
              exact Nat.le_trans (Nat.sub_le_sub_right hle n)
                (by
                  cases n with
                  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
                  | succ n' =>
                    rw [Nat.succ_sub_succ_eq_sub]
                    exact Nat.sub_le f n')
            rw [ih _ hdrop_init hdrop_le]
    have hlen : (extractInitBvBytes bs).length = bs.length :=
      (length_extractInitBvBytes_eq_iff bs).mpr hinit
    unfold Anneal.ListChunks.chunksOf
    rw [ite_false_of (Nat.ne_of_gt hn), ite_false_of (Nat.ne_of_gt hn), hlen]
    exact haux bs.length bs hinit (Nat.le_refl _)

/-- `Trusted.MirSemantics.leBytesOfNat` equals `Anneal.LeBytes.toLeBytesAux`
mapped through `UInt8.ofBitVec`. -/
theorem leBytesOfNat_eq_map : ∀ (n v : Nat),
    leBytesOfNat n v =
      (Anneal.LeBytes.toLeBytesAux n v).map UInt8.ofBitVec
  | 0, _ => rfl
  | n + 1, v => by
      have hHead : UInt8.ofNat (Nat.mod v 256) =
          UInt8.ofBitVec (BitVec.ofNat 8 v) := by
        apply congrArg UInt8.ofBitVec
        apply Anneal.BitVec.eq_of_toNat_eq
        change (BitVec.ofNat 8 (Nat.mod v 256)).toNat = (BitVec.ofNat 8 v).toNat
        rw [Anneal.BitVec.toNat_ofNat, Anneal.BitVec.toNat_ofNat, nat_mod_mod]
      change UInt8.ofNat (Nat.mod v 256) :: leBytesOfNat n (Nat.div v 256) =
        UInt8.ofBitVec (BitVec.ofNat 8 v) ::
          (Anneal.LeBytes.toLeBytesAux n (Nat.div v 256)).map UInt8.ofBitVec
      rw [hHead, leBytesOfNat_eq_map n (Nat.div v 256)]

/-- `Trusted.MirSemantics.encodeUInt .little` equals `Anneal.LeBytes.toLeBytes`
mapped through `UInt8.ofBitVec`. -/
theorem encodeUInt_little_eq_toLeBytes (n : Nat) (x : BitVec (n * 8)) :
    encodeUInt .little n x.toNat =
      (Anneal.LeBytes.toLeBytes n x).map UInt8.ofBitVec :=
  leBytesOfNat_eq_map n x.toNat

/-- `Trusted.MirSemantics.encodeUInt .big` equals `Anneal.LeBytes.toBeBytes`
mapped through `UInt8.ofBitVec`. -/
theorem encodeUInt_big_eq_toBeBytes (n : Nat) (x : BitVec (n * 8)) :
    encodeUInt .big n x.toNat =
      (Anneal.LeBytes.toBeBytes n x).map UInt8.ofBitVec := by
  unfold encodeUInt Anneal.LeBytes.toBeBytes Anneal.LeBytes.toLeBytes
  rw [leBytesOfNat_eq_map, list_map_reverse]

/-- `Trusted.MirSemantics.natOfLeBytes` on `bs.map UInt8.ofBitVec` equals
`Anneal.LeBytes.fromLeBytes bs`. -/
theorem natOfLeBytes_map_eq_fromLeBytes : ∀ (bs : List (BitVec 8)),
    natOfLeBytes (bs.map UInt8.ofBitVec) = Anneal.LeBytes.fromLeBytes bs
  | [] => rfl
  | b :: rest => by
    change (UInt8.ofBitVec b).toNat +
        256 * natOfLeBytes (rest.map UInt8.ofBitVec) =
      b.toNat + 256 * Anneal.LeBytes.fromLeBytes rest
    rw [natOfLeBytes_map_eq_fromLeBytes rest]
    rfl

private theorem natOfLeBytes_eq_fromLeBytes_toBitVec : ∀ (bs : List UInt8),
    natOfLeBytes bs = Anneal.LeBytes.fromLeBytes (bs.map UInt8.toBitVec)
  | [] => rfl
  | b :: rest => by
    change b.toNat + 256 * natOfLeBytes rest =
      b.toBitVec.toNat + 256 * Anneal.LeBytes.fromLeBytes (rest.map UInt8.toBitVec)
    rw [natOfLeBytes_eq_fromLeBytes_toBitVec rest]
    rfl

/-- `Trusted.MirSemantics.decodeUInt .little` agrees with
`Anneal.LeBytes.fromLeBytes`. -/
theorem decodeUInt_little_eq_fromLeBytes (bs : List (BitVec 8)) :
    decodeUInt .little (bs.map UInt8.ofBitVec) =
      Anneal.LeBytes.fromLeBytes bs :=
  natOfLeBytes_map_eq_fromLeBytes bs

/-- `Trusted.MirSemantics.decodeUInt .big` agrees with
`Anneal.LeBytes.fromBeBytes`. -/
theorem decodeUInt_big_eq_fromBeBytes (bs : List (BitVec 8)) :
    decodeUInt .big (bs.map UInt8.ofBitVec) =
      Anneal.LeBytes.fromBeBytes bs := by
  unfold decodeUInt Anneal.LeBytes.fromBeBytes
  dsimp only
  rw [← list_map_reverse, natOfLeBytes_map_eq_fromLeBytes]

private theorem list_reverse_reverse_ui {α : Type} :
    ∀ xs : List α, xs.reverse.reverse = xs
  | [] => rfl
  | x :: rest => by
    rw [List.reverse_cons, list_reverse_append, list_reverse_reverse_ui rest]
    rfl

private theorem list_length_reverse_ui {α : Type} (xs : List α) :
    xs.reverse.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    rw [List.reverse_cons, list_length_append, ih, List.length_cons,
      List.length_cons, List.length_nil, Nat.zero_add]

/-- Every decoded `UInt8` list fits strictly below `2 ^ (bs.length * 8)`. -/
theorem decodeUInt_lt_two_pow (endian : TargetEndian) (bs : List UInt8) :
    decodeUInt endian bs < Nat.pow 2 (bs.length * 8) := by
  cases endian with
  | little =>
    change natOfLeBytes bs < _
    rw [natOfLeBytes_eq_fromLeBytes_toBitVec]
    have hLt := Anneal.LeBytes.fromLeBytes_lt (bs.map UInt8.toBitVec)
    rw [list_length_map] at hLt
    exact hLt
  | big =>
    change natOfLeBytes bs.reverse < _
    rw [natOfLeBytes_eq_fromLeBytes_toBitVec]
    have hLt := Anneal.LeBytes.fromLeBytes_lt (bs.reverse.map UInt8.toBitVec)
    rw [list_length_map, list_length_reverse_ui] at hLt
    exact hLt

/-- Full round-trip: encoding `v` at `n` bytes and decoding with matching
endianness recovers `v % 2 ^ (n * 8)`. -/
theorem decodeUInt_encodeUInt (endian : TargetEndian) (n v : Nat) :
    decodeUInt endian (encodeUInt endian n v) =
      Nat.mod v (Nat.pow 2 (n * 8)) := by
  cases endian with
  | little =>
    unfold decodeUInt encodeUInt
    dsimp only
    rw [leBytesOfNat_eq_map, natOfLeBytes_map_eq_fromLeBytes,
      Anneal.LeBytes.fromLeBytes_toLeBytesAux]
    rfl
  | big =>
    unfold decodeUInt encodeUInt
    dsimp only
    rw [list_reverse_reverse_ui, leBytesOfNat_eq_map,
      natOfLeBytes_map_eq_fromLeBytes, Anneal.LeBytes.fromLeBytes_toLeBytesAux]
    rfl

/-- Right inverse: encoding a byte list's decoded value at its exact length
recovers the original `List UInt8` for both `.little` and `.big`. -/
theorem encodeUInt_decodeUInt (endian : TargetEndian) (bs : List UInt8) :
    encodeUInt endian bs.length (decodeUInt endian bs) = bs := by
  have hMapId : ∀ xs : List UInt8,
      (xs.map UInt8.toBitVec).map UInt8.ofBitVec = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      have hx : UInt8.ofBitVec x.toBitVec = x := rfl
      rw [List.map_cons, List.map_cons, ih, hx]
  cases endian with
  | little =>
    unfold encodeUInt decodeUInt
    dsimp only
    rw [leBytesOfNat_eq_map, natOfLeBytes_eq_fromLeBytes_toBitVec]
    have hL : (bs.map UInt8.toBitVec).length = bs.length := list_length_map _ _
    rw [← hL, Anneal.LeBytes.toLeBytesAux_fromLeBytes, hMapId bs]
  | big =>
    unfold encodeUInt decodeUInt
    dsimp only
    rw [leBytesOfNat_eq_map, natOfLeBytes_eq_fromLeBytes_toBitVec]
    have hL : (bs.reverse.map UInt8.toBitVec).length = bs.length := by
      rw [list_length_map, list_length_reverse_ui]
    rw [← hL, Anneal.LeBytes.toLeBytesAux_fromLeBytes, hMapId bs.reverse,
      list_reverse_reverse_ui]

/-- Splitting an `(m + n)`-byte little-endian `leBytesOfNat` sequence produces
low `m` bytes and high `n` bytes (`a % 2^(8*m)` and `a / 2^(8*m)`). -/
theorem leBytesOfNat_append_eq {m n : Nat} {a : Nat}
    (ha : a < Nat.pow 2 (m * 8)) (b : Nat) :
    leBytesOfNat m a ++ leBytesOfNat n b =
      leBytesOfNat (m + n) (a + Nat.pow 2 (m * 8) * b) := by
  have hMod : Nat.mod (a + Nat.pow 2 (m * 8) * b) (Nat.pow 2 (m * 8)) = a := by
    rw [nat_add_mul_mod_self_left]
    exact nat_mod_eq_of_lt ha
  have hDiv : Nat.div (a + Nat.pow 2 (m * 8) * b) (Nat.pow 2 (m * 8)) = b := by
    rw [nat_add_mul_div_left _ _ (nat_two_pow_pos _), nat_div_eq_of_lt ha,
      Nat.zero_add]
  have hModBytes : Anneal.LeBytes.toLeBytesAux m
      (Nat.mod (a + Nat.pow 2 (m * 8) * b) (Nat.pow 2 (m * 8))) =
      Anneal.LeBytes.toLeBytesAux m (a + Nat.pow 2 (m * 8) * b) := by
    have h := Anneal.LeBytes.toLeBytesAux_fromLeBytes
      (Anneal.LeBytes.toLeBytesAux m (a + Nat.pow 2 (m * 8) * b))
    rw [Anneal.LeBytes.toLeBytesAux_length,
      Anneal.LeBytes.fromLeBytes_toLeBytesAux] at h
    exact h
  have hDiv' : HDiv.hDiv (a + Nat.pow 2 (m * 8) * b) (HPow.hPow 2 (m * 8)) = b :=
    hDiv
  rw [leBytesOfNat_eq_map, leBytesOfNat_eq_map, leBytesOfNat_eq_map,
    ← list_map_append, Anneal.LeBytes.toLeBytesAux_add, hDiv', ← hModBytes, hMod]

/-- `initBytes?` succeeds on any `bs.map (allocByteOfBv prov)`. -/
theorem initBytes?_map_allocByteOfBv (prov : Option AllocId) :
    ∀ bs : List (BitVec 8),
      initBytes? (bs.map (allocByteOfBv prov)) =
        some (bs.map UInt8.ofBitVec)
  | [] => rfl
  | b :: rest => by
    change (match initBytes? (rest.map (allocByteOfBv prov)) with
      | some us => some (UInt8.ofBitVec b :: us)
      | none => none) = _
    rw [initBytes?_map_allocByteOfBv prov rest]
    rfl

private theorem initBytes?_of_allBytesInit :
    ∀ bs : List AllocByte,
      allBytesInit bs = true →
      ∃ us : List UInt8,
        initBytes? bs = some us ∧
        us.length = bs.length ∧
        us.map UInt8.toBitVec = extractInitBvBytes bs
  | [], _ => ⟨[], rfl, rfl, rfl⟩
  | .uninit :: _, h => nomatch h
  | .init b _ :: rest, h => by
    let ⟨us, hInit, hLen, hMap⟩ := initBytes?_of_allBytesInit rest h
    refine ⟨b :: us, ?_, ?_, ?_⟩
    · change (match initBytes? rest with
        | some bs' => some (b :: bs')
        | none => none) = some (b :: us)
      rw [hInit]
    · rw [List.length_cons, List.length_cons, hLen]
    · rw [List.map_cons]
      exact congrArg (List.cons b.toBitVec) hMap

private theorem initBytes?_map_init_none_self :
    ∀ bs : List UInt8,
      initBytes? (bs.map (fun b => AllocByte.init b none)) = some bs
  | [] => rfl
  | b :: rest => by
    change (match initBytes? (rest.map (fun b => AllocByte.init b none)) with
      | some us => some (b :: us)
      | none => none) = _
    rw [initBytes?_map_init_none_self rest]

/-- `encodeVal endian (.int w s) (.scalar (bvToScalar w s x))` always
succeeds with `(encodeUInt endian w.byteSize x.toNat).map (AllocByte.init ·
none)`. -/
theorem encodeVal_bvToScalar (endian : TargetEndian) (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    encodeVal endian (.int w s) (.scalar (bvToScalar w s x)) =
      .ok ((encodeUInt endian w.byteSize x.toNat).map
        (fun b => AllocByte.init b none)) := by
  unfold encodeVal
  rw [checkVal_bvToScalar w s x]
  dsimp only
  rw [Bool.not_true, if_false_eq, bvToScalar_bits_toNat w s x]

/-- Exact round-trip: `encodeVal` followed by `decodeVal` on any `bvToScalar w s
x` recovers `.ok (some (.scalar (bvToScalar w s x)))` for both `.little` and
`.big` `TargetEndian` (including `profileTargetEndian`). -/
theorem decodeVal_encodeVal_bvToScalar (endian : TargetEndian) (w : IntWidth)
    (s : Bool) (x : BitVec (8 * w.byteSize)) :
    ∃ bytes : List AllocByte,
      encodeVal endian (.int w s) (.scalar (bvToScalar w s x)) = .ok bytes ∧
      decodeVal endian (.int w s) bytes =
        .ok (some (.scalar (bvToScalar w s x))) := by
  let raw := encodeUInt endian w.byteSize x.toNat
  let bytes := raw.map (fun b => AllocByte.init b none)
  refine ⟨bytes, encodeVal_bvToScalar endian w s x, ?_⟩
  unfold decodeVal
  have hLayout : layoutOfTy (.int w s) = some (intLayout w) := rfl
  have hSize : (intLayout w).size = w.byteSize := by cases w <;> rfl
  have hRawLen : raw.length = w.byteSize := by
    cases endian with
    | little =>
      change (leBytesOfNat w.byteSize x.toNat).length = w.byteSize
      rw [leBytesOfNat_eq_map, list_length_map,
        Anneal.LeBytes.toLeBytesAux_length]
    | big =>
      change (leBytesOfNat w.byteSize x.toNat).reverse.length = w.byteSize
      rw [list_length_reverse_ui, leBytesOfNat_eq_map, list_length_map,
        Anneal.LeBytes.toLeBytesAux_length]
  have hBytesLen : bytes.length = w.byteSize := by
    change (raw.map _).length = w.byteSize
    rw [list_length_map, hRawLen]
  have hLenBeq : (!Nat.beq bytes.length (intLayout w).size) = false := by
    rw [hBytesLen, hSize, nat_beq_refl]
    rfl
  have hZeroBeq : Nat.beq (intLayout w).size 0 = false := by
    cases w <;> rfl
  dsimp only
  rw [hLayout]
  dsimp only
  rw [hLenBeq, if_false_eq, hZeroBeq, if_false_eq]
  change (match initBytes? (raw.map (fun b => AllocByte.init b none)) with
    | none => Except.ok none
    | some raw' =>
      match evalConstLit (.int w s)
          (.scalar (BitVec.ofNat 128 (decodeUInt endian raw'))) with
      | Except.ok v => Except.ok (some v)
      | Except.error k => Except.error k) = _
  rw [initBytes?_map_init_none_self]
  dsimp only
  have hDec : decodeUInt endian raw = x.toNat := by
    change decodeUInt endian (encodeUInt endian w.byteSize x.toNat) = x.toNat
    rw [decodeUInt_encodeUInt, Nat.mul_comm w.byteSize 8]
    exact Nat.mod_eq_of_lt x.isLt
  rw [hDec]
  unfold evalConstLit
  have hw : 8 * w.byteSize ≤ 128 := by
    rw [← intWidth_bitWidth_eq_eight_mul]
    exact intWidth_bitWidth_le_128 w
  have hx128 : x.toNat < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le x.isLt
      (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  have hTruncEq : truncateBits w (BitVec.ofNat 128 x.toNat) =
      BitVec.ofNat 128 x.toNat := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [toNat_truncateBits, intWidthModulus_eq_pow_eight,
      Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hx128]
    exact nat_mod_eq_of_lt x.isLt
  have hBneFalse : (truncateBits w (BitVec.ofNat 128 x.toNat) !=
      BitVec.ofNat 128 x.toNat) = false := by
    change (!(truncateBits w (BitVec.ofNat 128 x.toNat) ==
        BitVec.ofNat 128 x.toNat)) = false
    rw [hTruncEq, beq_self_eq_true]
    rfl
  dsimp only
  rw [hBneFalse, if_false_eq, hTruncEq]
  have hZext : BitVec.ofNat 128 x.toNat = bvZeroExtend 128 x := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hx128,
      toNat_bvZeroExtend_of_le hw]
  rw [hZext]
  rfl

end Anneal.Core

end
