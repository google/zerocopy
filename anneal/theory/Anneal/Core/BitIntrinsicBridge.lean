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
public import Anneal.ClassicalEm
public import Anneal.Core.BitVecMirBridge
public import Anneal.Core.BitVecMirBridgeExt

public section

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics Anneal.InitLemmas

/-!
# Intrinsic Bit-Operation, Endian Swap, Saturating, and Chunk Codec Bridges

Bridges pure bitvector intrinsic specifications and array-chunk codecs over the
`Anneal.BitVec` / `Anneal.BitVecArith` / `Anneal.LeBytes` / `Anneal.ListChunks`
algebraic stack into the operational MIR semantics (`Trusted.MirSemantics.Ops`,
`Trusted.MirSemantics.Bytes`) via `Anneal.Core.BitVecMirBridge` and
`Anneal.Core.BitVecMirBridgeExt`:

1. **Bit-Reversal (`bvBitreverse`), `bvCtlz`, `bvCttz`, Alignment & `Tnum`:**
   involution and bitwise homomorphisms for `bvBitreverse`, `bvCtlz` / `bvCttz`
   bounds and witness-bit characterizations, power-of-two alignment mask and
   modulo equivalences (`k ≤ bvCttz x ↔ and x (lowMask w k) = 0 ↔
   x.toNat % 2^k = 0`), `MaskEq` lower/upper bounds on `bvCttz` and `bvCtlz`,
   and `IntWidth` / `bvToScalar` nonzero bridges.
2. **Population Count (`bvPopcount`), Kernighan Step & `isPow2` Equivalence:**
   width bounds, complement (`w - bvPopcount x`), inclusion-exclusion
   (`or` + `and`), disjoint-OR additivity, `lowMask` counts, bit-reversal
   invariance, Kernighan step (`bvPopcount (and x (x - 1)) + 1 = bvPopcount x`),
   and exact three-way equivalence between `x ≠ 0 ∧ and x (x - 1) = 0`,
   `bvPopcount x = 1`, and `∃ k < w, x = BitVec.ofNat w (2^k)`.
3. **Byte-Swap (`bvBswap`) & Cross-Endian Serialization Equivalence:** exact
   byte-list reversal equivalence between `Anneal.BitVecArith.bswapBytes` and
   `Anneal.LeBytes.{toLeBytes,toBeBytes,fromBeBytes}`, the generic `IntWidth`
   law (`bvBswap_toLeBytes_eq`) plus the `.i8` identity (`bvBswap_i8`), and
   cross-endian `encodeVal` / `decodeVal` round-trips on initialized memory
   bytes.
4. **Saturating Arithmetic & Exact Division:** clamping bounds, monotonicity,
   and MIR `evalBinOp` agreement for unsigned and signed `saturatingAdd` /
   `saturatingSub`, plus multiplicative inverse and cancellation laws for
   unsigned and signed `exactDiv` with `evalBinOp .div`.
5. **Typed Scalar List Codecs over `ListChunks.chunksOf`:** byte-length
   preservation, exact chunk partitioning, `AllocByte` / `decodeVal` chunk
   bridges, and round-trip inversion for `encodeBvListBytes` and
   `decodeBvListBytes` under both `.little` and `.big` `TargetEndian`.
-/

/-! ## Part 0: Foundation-Only `Nat`, `Int`, `List`, and `BitVec` Helpers -/

private theorem bv_ite_bool_false_eq {α : Type} {c : Bool} {a b : α}
    (h : c = false) : (if c = true then a else b) = b := by
  rw [h]
  rfl

private theorem bv_ite_bool_true_eq {α : Type} {c : Bool} {a b : α}
    (h : c = true) : (if c = true then a else b) = a := by
  rw [h]
  rfl

private theorem bv_ite_cond_false {α : Type} {c : Bool} {a b : α}
    (h : c = false) : (if c then a else b) = b := by
  rw [h]
  rfl

private theorem bv_ite_cond_true {α : Type} {a b : α} :
    (if true then a else b) = a := rfl

private theorem nat_pow_zero (a : Nat) : Nat.pow a 0 = 1 := rfl

private theorem bitVec_toNat_lt_pow {w : Nat} (x : BitVec w) :
    x.toNat < Nat.pow 2 w :=
  x.isLt

private theorem nat_add_mod_left (x y : Nat) :
    Nat.mod (x + y) y = Nat.mod x y :=
  Nat.add_mod_right x y

private theorem nat_sub_right_comm (a b c : Nat) :
    a - b - c = a - c - b := by
  rw [Nat.sub_sub, Nat.add_comm b c, ← Nat.sub_sub]

private theorem nat_sub_lt_of_lt_add {a b c : Nat}
    (hb : 0 < b) (h : a < b + c) : a - c < b := by
  cases Nat.lt_or_ge a c with
  | inl hlt =>
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
    exact hb
  | inr hge =>
    have hlt : (a - c) + c < b + c := by
      rw [Nat.sub_add_cancel hge]
      exact h
    have h1 : (a - c + 1) + c ≤ b + c := by
      rw [Nat.add_right_comm]
      exact hlt
    exact Nat.le_of_add_le_add_right h1

private theorem nat_sub_le_sub {a b c d : Nat}
    (hab : a ≤ b) (hcd : d ≤ c) : a - c ≤ b - d :=
  Nat.le_trans (Nat.sub_le_sub_right hab c) (Nat.sub_le_sub_left hcd b)

private theorem nat_pow_succ (a n : Nat) :
    Nat.pow a (n + 1) = Nat.pow a n * a :=
  Nat.pow_succ a n

private theorem nat_two_pow_split {w : Nat} (hw : 0 < w) :
    Nat.pow 2 w = Nat.pow 2 (w - 1) + Nat.pow 2 (w - 1) := by
  have hEq : w = (w - 1) + 1 := Eq.symm (Nat.sub_add_cancel hw)
  have hP := congrArg (Nat.pow 2) hEq
  rw [nat_pow_succ, Nat.mul_two] at hP
  exact hP

private theorem nat_div_zero (a : Nat) : Nat.div a 0 = 0 :=
  Nat.div_zero a

private theorem nat_div_one (a : Nat) : Nat.div a 1 = a :=
  Nat.div_one a

private theorem nat_zero_div (b : Nat) : Nat.div 0 b = 0 :=
  Nat.zero_div b

private theorem nat_zero_mod (b : Nat) : Nat.mod 0 b = 0 :=
  Nat.zero_mod b

private theorem nat_mod_one (a : Nat) : Nat.mod a 1 = 0 :=
  Nat.mod_one a

private theorem nat_mod_zero (a : Nat) : Nat.mod a 0 = a :=
  Nat.mod_zero a

private theorem nat_mod_self (a : Nat) : Nat.mod a a = 0 :=
  Nat.mod_self a

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_div_div_eq_div_mul (m n k : Nat) :
    Nat.div (Nat.div m n) k = Nat.div m (n * k) :=
  Nat.div_div_eq_div_mul m n k

private theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

private theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_mul_mod_right (m n : Nat) : Nat.mod (m * n) m = 0 :=
  Nat.mul_mod_right m n

private theorem nat_mul_div_right (n : Nat) {m : Nat} (hm : 0 < m) :
    Nat.div (m * n) m = n :=
  Nat.mul_div_right n hm

private theorem nat_mul_div_left (m : Nat) {n : Nat} (hn : 0 < n) :
    Nat.div (m * n) n = m :=
  Nat.mul_div_left m hn

private theorem nat_div_lt_iff_lt_mul {x y k : Nat} (hk : 0 < k) :
    Nat.div x k < y ↔ x < y * k :=
  Nat.div_lt_iff_lt_mul hk

private theorem nat_lt_of_add_lt_add_right {a b c : Nat}
    (h : a + c < b + c) : a < b := by
  have h1 : (a + 1) + c ≤ b + c := by
    rw [Nat.add_right_comm]
    exact h
  exact Nat.le_of_add_le_add_right h1

private theorem nat_sub_sub_self {a b : Nat} (h : a ≤ b) :
    b - (b - a) = a := by
  have h1 : (b - a) + a = b := Nat.sub_add_cancel h
  have h2 := congrArg (fun z => z - (b - a)) h1
  rw [Nat.add_comm (b - a) a, Nat.add_sub_cancel] at h2
  exact Eq.symm h2

private theorem nat_sub_add_comm {a b c : Nat} (h : b ≤ a) :
    a - b + c = a + c - b := by
  have h1 : (a - b + c) + b = a + c := by
    rw [Nat.add_right_comm, Nat.sub_add_cancel h]
  have h2 := congrArg (fun z => z - b) h1
  rw [Nat.add_sub_cancel] at h2
  exact h2

private theorem nat_testBit_eq (m i : Nat) :
    m.testBit i = decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) := by
  unfold Nat.testBit
  have hsr : Nat.shiftRight m i = Nat.div m (Nat.pow 2 i) :=
    Nat.shiftRight_eq_div_pow m i
  change (Nat.land 1 (Nat.shiftRight m i) != 0) = _
  rw [hsr]
  have hland : Nat.land 1 (Nat.div m (Nat.pow 2 i)) =
      if decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) then 1 else 0 := by
    rw [Anneal.NatBitwise.land_eq_bitwise, Anneal.NatBitwise.unfold_eq]
    cases hq : Nat.div m (Nat.pow 2 i) with
    | zero => rfl
    | succ q' =>
      have hdiv1 : Nat.div 1 2 = 0 := by decide
      have hmod1 : decide (Nat.mod 1 2 = 1) = true := by decide
      have hbw0 : Nat.bitwise and 0 (Nat.div (Nat.succ q') 2) = 0 := by
        rw [Anneal.NatBitwise.unfold_eq]
        rfl
      rw [ite_false_of (by decide : ¬ (1 = 0)),
        ite_false_of (fun h => nomatch h)]
      dsimp only
      rw [hdiv1, hbw0, hmod1]
      cases decide (Nat.mod (Nat.succ q') 2 = 1) <;> rfl
  rw [hland]
  cases decide (Nat.mod (Nat.div m (Nat.pow 2 i)) 2 = 1) <;> rfl

private theorem nat_testBit_zero_bit (m : Nat) :
    m.testBit 0 = decide (Nat.mod m 2 = 1) := by
  rw [nat_testBit_eq, nat_pow_zero, nat_div_one]

private theorem nat_testBit_succ (m i : Nat) :
    m.testBit (i + 1) = (Nat.div m 2).testBit i := by
  rw [nat_testBit_eq, nat_testBit_eq, nat_div_div_eq_div_mul,
    Nat.mul_comm 2 (Nat.pow 2 i), ← nat_pow_succ]

private theorem nat_testBit_add (m a b : Nat) :
    m.testBit (a + b) = (Nat.div m (Nat.pow 2 a)).testBit b := by
  rw [nat_testBit_eq, nat_testBit_eq, nat_pow_add, nat_div_div_eq_div_mul]

private theorem nat_testBit_two_pow (k i : Nat) :
    (Nat.pow 2 k).testBit i = decide (i = k) := by
  rw [nat_testBit_eq]
  cases Nat.lt_trichotomy i k with
  | inl hlt =>
    have hne : i ≠ k := Nat.ne_of_lt hlt
    rw [decide_eq_false hne]
    let d := k - (i + 1)
    have hk : k = i + (d + 1) := by
      have h1 : i + 1 ≤ k := hlt
      have h2 := Nat.add_sub_of_le h1
      rw [Nat.add_assoc, Nat.add_comm 1 d] at h2
      exact h2.symm
    have hPow : Nat.pow 2 k = Nat.pow 2 i * (2 * Nat.pow 2 d) := by
      rw [hk, nat_pow_add, nat_pow_succ, Nat.mul_comm (Nat.pow 2 d) 2]
    rw [hPow, nat_mul_div_right _ (nat_two_pow_pos i), nat_mul_mod_right]
    rfl
  | inr hor =>
    cases hor with
    | inl heq =>
      subst heq
      rw [decide_eq_true rfl]
      have h1 : Nat.div (Nat.pow 2 i) (Nat.pow 2 i) = 1 :=
        Nat.div_self (nat_two_pow_pos i)
      rw [h1]
      rfl
    | inr hgt =>
      have hne : i ≠ k := Nat.ne_of_gt hgt
      rw [decide_eq_false hne]
      have hlt : Nat.pow 2 k < Nat.pow 2 i := by
        have hk1 : k + 1 ≤ i := hgt
        have hpos : 0 < Nat.pow 2 k := nat_two_pow_pos k
        have h1 : Nat.pow 2 k < Nat.pow 2 (k + 1) := by
          rw [nat_pow_succ, Nat.mul_two]
          exact Nat.lt_add_of_pos_right hpos
        exact Nat.lt_of_lt_of_le h1
          (Nat.pow_le_pow_right (by decide : 0 < 2) hk1)
      rw [nat_div_eq_of_lt hlt, nat_zero_mod]
      rfl

private theorem nat_mod_two_cases (n : Nat) :
    Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hlt : Nat.mod n 2 < 2 := Nat.mod_lt n (by decide)
  cases hm : Nat.mod n 2 with
  | zero => left; rfl
  | succ k =>
    cases k with
    | zero => right; rfl
    | succ k' =>
      rw [hm] at hlt
      exact False.elim (Nat.not_lt_of_ge
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k'))) hlt)

private theorem nat_mod_two_pow_eq_zero_iff_testBit (n : Nat) :
    ∀ k : Nat, Nat.mod n (Nat.pow 2 k) = 0 ↔
      ∀ i : Nat, i < k → n.testBit i = false
  | 0 => by
    rw [nat_pow_zero, nat_mod_one]
    constructor
    · intro _ i hi
      exact False.elim (Nat.not_lt_zero i hi)
    · intro _
      rfl
  | k + 1 => by
    have ih := nat_mod_two_pow_eq_zero_iff_testBit (Nat.div n 2) k
    have hsplit : n = Nat.pow 2 (k + 1) * Nat.div (Nat.div n 2) (Nat.pow 2 k) +
        (2 * Nat.mod (Nat.div n 2) (Nat.pow 2 k) + Nat.mod n 2) := by
      have h1 : n = 2 * Nat.div n 2 + Nat.mod n 2 :=
        Eq.symm (nat_div_add_mod n 2)
      have h2 : Nat.div n 2 = Nat.pow 2 k * Nat.div (Nat.div n 2) (Nat.pow 2 k) +
          Nat.mod (Nat.div n 2) (Nat.pow 2 k) :=
        Eq.symm (nat_div_add_mod (Nat.div n 2) (Nat.pow 2 k))
      rw [h2, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (Nat.pow 2 k),
        ← nat_pow_succ, Nat.add_assoc] at h1
      exact h1
    have hremLt : 2 * Nat.mod (Nat.div n 2) (Nat.pow 2 k) + Nat.mod n 2 <
        Nat.pow 2 (k + 1) := by
      have hm1 : Nat.mod (Nat.div n 2) (Nat.pow 2 k) ≤ Nat.pow 2 k - 1 :=
        Nat.le_sub_one_of_lt (Nat.mod_lt _ (nat_two_pow_pos k))
      have hm2 : Nat.mod n 2 ≤ 1 := by
        cases nat_mod_two_cases n with
        | inl h0 => rw [h0]; exact Nat.zero_le 1
        | inr h1 => rw [h1]; exact Nat.le_refl 1
      have hle : 2 * Nat.mod (Nat.div n 2) (Nat.pow 2 k) + Nat.mod n 2 ≤
          2 * (Nat.pow 2 k - 1) + 1 :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hm1) hm2
      have hEq : 2 * (Nat.pow 2 k - 1) + 1 + 1 = Nat.pow 2 (k + 1) := by
        have hpos : 0 < Nat.pow 2 k := nat_two_pow_pos k
        rw [Nat.mul_sub_left_distrib, Nat.mul_one,
          Nat.add_assoc, (by decide : 1 + 1 = 2),
          Nat.sub_add_cancel (Nat.mul_le_mul_left 2 hpos),
          nat_pow_succ, Nat.mul_comm]
      exact Nat.lt_of_le_of_lt hle (by
        rw [← hEq]
        exact Nat.lt_succ_self _)
    have hModEq : Nat.mod n (Nat.pow 2 (k + 1)) =
        2 * Nat.mod (Nat.div n 2) (Nat.pow 2 k) + Nat.mod n 2 := by
      have hC := congrArg (fun z => Nat.mod z (Nat.pow 2 (k + 1))) hsplit
      rw [Nat.add_comm (Nat.pow 2 (k + 1) * _),
        nat_add_mul_mod_self_left, nat_mod_eq_of_lt hremLt] at hC
      exact hC
    constructor
    · intro hmod i hi
      rw [hModEq] at hmod
      have hdiv0 : Nat.mod (Nat.div n 2) (Nat.pow 2 k) = 0 := by
        cases h0 : Nat.mod (Nat.div n 2) (Nat.pow 2 k) with
        | zero => rfl
        | succ m =>
          rw [h0] at hmod
          have hpos : 0 < 2 * (m + 1) + Nat.mod n 2 := by
            rw [Nat.mul_succ]
            exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ (2 * m + 1))
              (Nat.le_add_right (2 * m + 2) (Nat.mod n 2))
          rw [hmod] at hpos
          exact False.elim (Nat.lt_irrefl 0 hpos)
      have hm0 : Nat.mod n 2 = 0 := by
        rw [hdiv0, Nat.mul_zero, Nat.zero_add] at hmod
        exact hmod
      cases i with
      | zero =>
        rw [nat_testBit_zero_bit, hm0]
        rfl
      | succ i' =>
        rw [nat_testBit_succ]
        exact ih.1 hdiv0 i' (Nat.lt_of_succ_lt_succ hi)
    · intro hall
      have h0 : n.testBit 0 = false := hall 0 (Nat.zero_lt_succ k)
      rw [nat_testBit_zero_bit] at h0
      have hm0 : Nat.mod n 2 = 0 := by
        cases nat_mod_two_cases n with
        | inl h => exact h
        | inr h => rw [h] at h0; nomatch h0
      have hdiv0 : Nat.mod (Nat.div n 2) (Nat.pow 2 k) = 0 := by
        apply ih.2
        intro i hi
        rw [← nat_testBit_succ]
        exact hall (i + 1) (Nat.succ_lt_succ hi)
      rw [hModEq, hdiv0, hm0]

private theorem int_ofNat_sub_ofNat (m n : Nat) :
    Int.ofNat m - Int.ofNat n = Int.subNatNat m n := by
  cases n with
  | zero =>
    change Int.ofNat m = Int.subNatNat m 0
    unfold Int.subNatNat
    rw [Nat.zero_sub, Nat.sub_zero]
  | succ _ => rfl

private theorem int_ofNat_le_iff {m n : Nat} :
    Int.ofNat m ≤ Int.ofNat n ↔ m ≤ n := by
  constructor
  · intro h
    change Int.NonNeg (Int.ofNat n - Int.ofNat m) at h
    rw [int_ofNat_sub_ofNat] at h
    unfold Int.subNatNat at h
    cases hSub : m - n with
    | zero => exact Nat.le_of_sub_eq_zero hSub
    | succ d => rw [hSub] at h; nomatch h
  · intro h
    change Int.NonNeg (Int.ofNat n - Int.ofNat m)
    rw [int_ofNat_sub_ofNat]
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le h]
    exact Int.NonNeg.mk (n - m)

private theorem int_ofNat_lt_iff {m n : Nat} :
    Int.ofNat m < Int.ofNat n ↔ m < n :=
  int_ofNat_le_iff

private theorem int_negSucc_le_negSucc_iff {m n : Nat} :
    Int.negSucc m ≤ Int.negSucc n ↔ n ≤ m := by
  constructor
  · intro h
    change Int.NonNeg (Int.subNatNat (m + 1) (n + 1)) at h
    unfold Int.subNatNat at h
    cases hSub : (n + 1) - (m + 1) with
    | zero => exact Nat.le_of_succ_le_succ (Nat.le_of_sub_eq_zero hSub)
    | succ d => rw [hSub] at h; nomatch h
  · intro h
    change Int.NonNeg (Int.subNatNat (m + 1) (n + 1))
    unfold Int.subNatNat
    rw [Nat.sub_eq_zero_of_le (Nat.succ_le_succ h)]
    exact Int.NonNeg.mk _

private theorem int_negSucc_le_ofNat (m n : Nat) :
    Int.negSucc m ≤ Int.ofNat n :=
  Int.NonNeg.mk _

private theorem int_not_ofNat_le_negSucc (m n : Nat) :
    ¬ (Int.ofNat m ≤ Int.negSucc n) := by
  intro h
  change Int.NonNeg (Int.negSucc n - Int.ofNat m) at h
  cases m with
  | zero =>
    change Int.NonNeg (Int.negSucc n) at h
    nomatch h
  | succ k =>
    have hEq : Int.negSucc n - Int.ofNat (k + 1) =
        Int.negSucc (n + k + 1) := rfl
    rw [hEq] at h
    nomatch h

private theorem int_le_antisymm {a b : Int} (hab : a ≤ b) (hba : b ≤ a) :
    a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [int_ofNat_le_iff] at hab hba
      exact congrArg Int.ofNat (Nat.le_antisymm hab hba)
    | negSucc n => exact False.elim (int_not_ofNat_le_negSucc m n hab)
  | negSucc m =>
    cases b with
    | ofNat n => exact False.elim (int_not_ofNat_le_negSucc n m hba)
    | negSucc n =>
      rw [int_negSucc_le_negSucc_iff] at hab hba
      exact congrArg Int.negSucc (Nat.le_antisymm hba hab)

private theorem int_not_lt_iff_le (a b : Int) : ¬ (a < b) ↔ b ≤ a := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [int_ofNat_lt_iff, int_ofNat_le_iff]
      exact ⟨Nat.le_of_not_lt, Nat.not_lt_of_ge⟩
    | negSucc n =>
      refine ⟨fun _ => int_negSucc_le_ofNat n m, fun _ hlt => ?_⟩
      change Int.NonNeg (Int.negSucc n - Int.ofNat (m + 1)) at hlt
      have hSub : Int.negSucc n - Int.ofNat (m + 1) =
          Int.negSucc (n + (m + 1)) := rfl
      rw [hSub] at hlt
      nomatch hlt
  | negSucc m =>
    cases b with
    | ofNat n =>
      refine ⟨fun h => False.elim (h ?_), fun h => ?_⟩
      · change Int.NonNeg (Int.ofNat n - (Int.negSucc m + 1))
        cases m with
        | zero =>
          change Int.NonNeg (Int.ofNat n - Int.ofNat 0)
          rw [int_ofNat_sub_ofNat]
          unfold Int.subNatNat
          rw [Nat.zero_sub]
          exact Int.NonNeg.mk n
        | succ m' =>
          have h1 : Int.negSucc (Nat.succ m') + 1 = Int.negSucc m' := rfl
          rw [h1]
          exact Int.NonNeg.mk _
      · exact False.elim (int_not_ofNat_le_negSucc n m h)
    | negSucc n =>
      have hLtIff : Int.negSucc m < Int.negSucc n ↔ n < m := by
        change Int.NonNeg (Int.negSucc n - (Int.negSucc m + 1)) ↔ _
        cases m with
        | zero =>
          constructor
          · intro h
            change Int.NonNeg (Int.negSucc n - Int.ofNat 0) at h
            have h0 : Int.negSucc n - Int.ofNat 0 = Int.negSucc n := rfl
            rw [h0] at h
            nomatch h
          · intro h
            exact False.elim (Nat.not_lt_zero n h)
        | succ m' =>
          have h1 : Int.negSucc (Nat.succ m') + 1 = Int.negSucc m' := rfl
          rw [h1]
          change Int.negSucc m' ≤ Int.negSucc n ↔ _
          rw [int_negSucc_le_negSucc_iff]
          exact ⟨Nat.lt_succ_of_le, Nat.le_of_lt_succ⟩
      rw [hLtIff, int_negSucc_le_negSucc_iff]
      exact ⟨Nat.le_of_not_lt, Nat.not_lt_of_ge⟩

private theorem int_not_le_iff_lt (a b : Int) : ¬ (a ≤ b) ↔ b < a := by
  constructor
  · intro h
    cases Anneal.ClassicalEm.prop_em (b < a) with
    | inl hlt => exact hlt
    | inr hnlt => exact False.elim (h ((int_not_lt_iff_le b a).mp hnlt))
  · intro hlt hle
    exact (int_not_lt_iff_le b a).mpr hle hlt

private theorem int_lt_or_ge (a b : Int) : a < b ∨ b ≤ a := by
  cases Anneal.ClassicalEm.prop_em (a < b) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr ((int_not_lt_iff_le a b).mp h)

private theorem intBalance_le_iff {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    x ≤ y ↔ px + ny ≤ py + nx := by
  unfold IntBalance at hx hy
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      dsimp only [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      rw [int_ofNat_le_iff]
      constructor
      · intro h
        have h1 : (a + nx) + ny ≤ (b + ny) + nx := by
          rw [Nat.add_assoc a nx ny, Nat.add_assoc b ny nx,
            Nat.add_comm ny nx]
          exact Nat.add_le_add_right h (nx + ny)
        rw [hx, hy] at h1
        exact h1
      · intro h
        rw [← hx, ← hy, Nat.add_assoc a nx ny, Nat.add_assoc b ny nx,
          Nat.add_comm ny nx] at h
        exact Nat.le_of_add_le_add_right h
    | negSucc b =>
      dsimp only [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      constructor
      · intro h
        exact False.elim (int_not_ofNat_le_negSucc a b h)
      · intro h
        have h1 : (a + nx) + (b + 1 + py) ≤ py + nx := by
          rw [hx, ← hy]
          exact h
        have h2 : (a + b + 1) + (py + nx) ≤ py + nx := by
          have hEq : (a + nx) + (b + 1 + py) = (a + b + 1) + (py + nx) := by
            rw [Nat.add_assoc a b 1, Nat.add_assoc a nx (b + 1 + py),
              Nat.add_comm nx (b + 1 + py), Nat.add_assoc (b + 1) py nx,
              ← Nat.add_assoc a (b + 1) (py + nx)]
          rw [← hEq]
          exact h1
        have h0 : a + b + 1 ≤ 0 := by
          have hZero : (a + b + 1) + (py + nx) ≤ 0 + (py + nx) := by
            rw [Nat.zero_add]
            exact h2
          exact Nat.le_of_add_le_add_right hZero
        exact False.elim (Nat.not_succ_le_zero (a + b) h0)
  | negSucc a =>
    cases y with
    | ofNat b =>
      dsimp only [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      refine ⟨fun _ => ?_, fun _ => int_negSucc_le_ofNat a b⟩
      have h1 : px + ny ≤ ((a + 1) + px) + (b + ny) := by
        have hEq : ((a + 1) + px) + (b + ny) = (a + 1 + b) + (px + ny) := by
          rw [add_four_rearrange (a + 1) px b ny]
        rw [hEq]
        exact Nat.le_add_left (px + ny) (a + 1 + b)
      rw [← hx, hy, Nat.add_comm nx py] at h1
      exact h1
    | negSucc b =>
      dsimp only [intPos, intNeg] at hx hy
      rw [Nat.zero_add] at hx hy
      rw [int_negSucc_le_negSucc_iff]
      constructor
      · intro h
        have h1 : px + (b + 1 + py) ≤ py + (a + 1 + px) := by
          have hL : px + (b + 1 + py) = (b + 1) + (px + py) := by
            rw [Nat.add_comm (b + 1) py, ← Nat.add_assoc px py (b + 1),
              Nat.add_comm (px + py) (b + 1)]
          have hR : py + (a + 1 + px) = (a + 1) + (px + py) := by
            rw [Nat.add_comm (a + 1) px, ← Nat.add_assoc py px (a + 1),
              Nat.add_comm py px, Nat.add_comm (px + py) (a + 1)]
          rw [hL, hR]
          exact Nat.add_le_add_right (Nat.succ_le_succ h) (px + py)
        rw [← hx, ← hy] at h1
        exact h1
      · intro h
        rw [hx, hy] at h
        have h1 : (b + 1) + (px + py) ≤ (a + 1) + (px + py) := by
          have hL : px + (b + 1 + py) = (b + 1) + (px + py) := by
            rw [Nat.add_comm (b + 1) py, ← Nat.add_assoc px py (b + 1),
              Nat.add_comm (px + py) (b + 1)]
          have hR : py + (a + 1 + px) = (a + 1) + (px + py) := by
            rw [Nat.add_comm (a + 1) px, ← Nat.add_assoc py px (a + 1),
              Nat.add_comm py px, Nat.add_comm (px + py) (a + 1)]
          rw [← hL, ← hR]
          exact h
        exact Nat.le_of_succ_le_succ (Nat.le_of_add_le_add_right h1)

private theorem intBalance_lt_iff {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    x < y ↔ px + ny < py + nx := by
  rw [← int_not_le_iff_lt, intBalance_le_iff hy hx]
  exact ⟨Nat.lt_of_not_le, Nat.not_le_of_gt⟩

private theorem intBalance_neg_of {x : Int} {p n : Nat}
    (h : IntBalance x p n) : IntBalance (Neg.neg x) n p := by
  unfold IntBalance at h
  unfold IntBalance
  cases x with
  | ofNat k =>
    cases k with
    | zero => exact h.symm
    | succ k' =>
      change (k' + 1) + n = 0 + p at h
      change 0 + p = (k' + 1) + n
      exact h.symm
  | negSucc k =>
    change 0 + n = (k + 1) + p at h
    change (k + 1) + p = 0 + n
    exact h.symm

private theorem intBalance_add_of {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (x + y) (px + py) (nx + ny) := by
  have hxEq : intPos x + nx = intNeg x + px := hx
  have hyEq : intPos y + ny = intNeg y + py := hy
  have hSum : IntBalance (x + y) (intPos x + intPos y) (intNeg x + intNeg y) := by
    cases x with
    | ofNat a =>
      cases y with
      | ofNat b => exact intBalance_ofNat (a + b)
      | negSucc b =>
        dsimp only [intPos, intNeg]
        rw [Nat.add_zero, Nat.zero_add]
        exact intBalance_subNatNat a (b + 1)
    | negSucc a =>
      cases y with
      | ofNat b =>
        dsimp only [intPos, intNeg]
        rw [Nat.zero_add, Nat.add_zero]
        exact intBalance_subNatNat b (a + 1)
      | negSucc b =>
        have hEq : Int.negSucc a + Int.negSucc b = Int.negSucc (a + b + 1) := rfl
        rw [hEq]
        dsimp only [IntBalance, intPos, intNeg]
        rw [Nat.zero_add, Nat.add_zero, ← Nat.add_assoc (a + 1) b 1,
          Nat.add_right_comm a 1 b]
  unfold IntBalance at hSum
  unfold IntBalance
  have hComb : (intPos (x + y) + (nx + ny)) + (intPos x + intPos y) +
      (intNeg x + intNeg y) =
      (intNeg (x + y) + (px + py)) + (intPos x + intPos y) +
      (intNeg x + intNeg y) := by
    have hL : (intPos (x + y) + (nx + ny)) + (intPos x + intPos y) +
        (intNeg x + intNeg y) =
        (intPos (x + y) + (intNeg x + intNeg y)) +
          ((intPos x + nx) + (intPos y + ny)) := by
      rw [Nat.add_assoc (intPos (x + y)) (nx + ny) (intPos x + intPos y),
        Nat.add_comm (nx + ny) (intPos x + intPos y),
        ← Nat.add_assoc (intPos (x + y)) (intPos x + intPos y) (nx + ny),
        Nat.add_assoc _ (nx + ny) (intNeg x + intNeg y),
        Nat.add_comm (nx + ny) (intNeg x + intNeg y),
        ← Nat.add_assoc _ (intNeg x + intNeg y) (nx + ny),
        Nat.add_assoc (intPos (x + y)) (intPos x + intPos y) (intNeg x + intNeg y),
        Nat.add_comm (intPos x + intPos y) (intNeg x + intNeg y),
        ← Nat.add_assoc (intPos (x + y)) (intNeg x + intNeg y) (intPos x + intPos y),
        Nat.add_assoc _ (intPos x + intPos y) (nx + ny),
        add_four_rearrange (intPos x) (intPos y) nx ny]
    have hR : (intNeg (x + y) + (px + py)) + (intPos x + intPos y) +
        (intNeg x + intNeg y) =
        (intNeg (x + y) + (intPos x + intPos y)) +
          ((intNeg x + px) + (intNeg y + py)) := by
      rw [Nat.add_assoc (intNeg (x + y)) (px + py) (intPos x + intPos y),
        Nat.add_comm (px + py) (intPos x + intPos y),
        ← Nat.add_assoc (intNeg (x + y)) (intPos x + intPos y) (px + py),
        Nat.add_assoc _ (px + py) (intNeg x + intNeg y),
        add_four_rearrange px py (intNeg x) (intNeg y),
        Nat.add_comm px (intNeg x), Nat.add_comm py (intNeg y)]
    rw [hL, hR, hSum, hxEq, hyEq]
  exact Nat.add_right_cancel (Nat.add_right_cancel hComb)

private theorem intBalance_sub_of {x y : Int} {px nx py ny : Nat}
    (hx : IntBalance x px nx) (hy : IntBalance y py ny) :
    IntBalance (x - y) (px + ny) (nx + py) :=
  intBalance_add_of hx (intBalance_neg_of hy)

private theorem list_length_reverse {α : Type} :
    ∀ xs : List α, xs.reverse.length = xs.length
  | [] => rfl
  | x :: rest => by
    rw [List.reverse_cons, List.length_append, List.length_cons,
      List.length_nil, list_length_reverse rest]
    rfl

private theorem list_append_nil {α : Type} :
    ∀ xs : List α, xs ++ [] = xs
  | [] => rfl
  | x :: rest => congrArg (List.cons x) (list_append_nil rest)

private theorem list_reverse_append {α : Type} :
    ∀ xs ys : List α, (xs ++ ys).reverse = ys.reverse ++ xs.reverse
  | [], ys => by
    rw [List.nil_append, List.reverse_nil, list_append_nil]
  | x :: xs, ys => by
    rw [List.cons_append, List.reverse_cons, List.reverse_cons,
      list_reverse_append xs ys, List.append_assoc]

private theorem list_getElem?_append_left {α : Type} :
    ∀ {xs ys : List α} {i : Nat}, i < xs.length → (xs ++ ys)[i]? = xs[i]?
  | [], _, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, hi =>
    list_getElem?_append_left (xs := xs) (ys := ys) (i := i)
      (Nat.lt_of_succ_lt_succ hi)

private theorem list_getElem?_append_right {α : Type} :
    ∀ {xs ys : List α} {i : Nat}, xs.length ≤ i →
      (xs ++ ys)[i]? = ys[i - xs.length]?
  | [], ys, i, _ => by
    rw [List.nil_append, List.length_nil, Nat.sub_zero]
  | _ :: _, _, 0, hle => False.elim (Nat.not_succ_le_zero _ hle)
  | _ :: xs, ys, i + 1, hle => by
    rw [List.cons_append, List.length_cons, Nat.succ_sub_succ]
    exact list_getElem?_append_right (Nat.le_of_succ_le_succ hle)

private theorem list_eq_nil_of_length_eq_zero {α : Type} :
    ∀ {xs : List α}, xs.length = 0 → xs = []
  | [], _ => rfl
  | _ :: _, h => by nomatch h

private theorem list_take_of_length_le {α : Type} :
    ∀ (xs : List α) (n : Nat), xs.length ≤ n → xs.take n = xs
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | x :: xs, n + 1, h =>
    congrArg (List.cons x) (list_take_of_length_le xs n (Nat.le_of_succ_le_succ h))

private theorem list_length_take_of_le {α : Type} :
    ∀ (xs : List α) (n : Nat), n ≤ xs.length → (xs.take n).length = n
  | [], 0, _ => rfl
  | [], _ + 1, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: _, 0, _ => rfl
  | _ :: xs, n + 1, h =>
    congrArg Nat.succ (list_length_take_of_le xs n (Nat.le_of_succ_le_succ h))

private theorem list_length_drop {α : Type} :
    ∀ (xs : List α) (n : Nat), (xs.drop n).length = xs.length - n
  | [], 0 => rfl
  | [], n + 1 => (Nat.zero_sub (n + 1)).symm
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => by
    change (xs.drop n).length = xs.length + 1 - (n + 1)
    rw [Nat.succ_sub_succ]
    exact list_length_drop xs n

private theorem list_take_append_drop {α : Type} :
    ∀ (xs : List α) (n : Nat), xs.take n ++ xs.drop n = xs
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | x :: xs, n + 1 =>
    congrArg (List.cons x) (list_take_append_drop xs n)

private theorem list_reverse_reverse {α : Type} :
    ∀ xs : List α, xs.reverse.reverse = xs
  | [] => rfl
  | x :: rest => by
    rw [List.reverse_cons, list_reverse_append, list_reverse_reverse rest]
    rfl

private theorem list_getElem?_reverse {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length →
      xs.reverse[i]? = xs[xs.length - 1 - i]?
  | [], _, hi => False.elim (Nat.not_lt_zero _ hi)
  | x :: rest, i, hi => by
    have hEq : (x :: rest).reverse = rest.reverse ++ [x] :=
      List.reverse_cons
    have hLen : rest.reverse.length = rest.length := list_length_reverse rest
    cases Nat.lt_or_ge i rest.length with
    | inl hlt =>
      have hGetApp :
          (rest.reverse ++ [x])[i]? = rest.reverse[i]? :=
        list_getElem?_append_left (by rw [hLen]; exact hlt)
      have hSubPos : 0 < rest.length - i := Nat.zero_lt_sub_of_lt hlt
      have hStep : (rest.length + 1) - 1 - i = (rest.length - 1 - i) + 1 := by
        rw [Nat.add_sub_cancel]
        have hSubEq : rest.length - i = (rest.length - 1 - i) + 1 := by
          have hc := Nat.sub_add_cancel hSubPos
          rw [Nat.sub_sub, Nat.add_comm i 1, ← Nat.sub_sub] at hc
          exact hc.symm
        exact hSubEq
      rw [hEq, hGetApp, list_getElem?_reverse rest i hlt, List.length_cons,
        hStep]
      rfl
    | inr hge =>
      have hiEq : i = rest.length :=
        Nat.le_antisymm (Nat.le_of_lt_succ (by
          rw [List.length_cons] at hi; exact hi)) hge
      subst hiEq
      have hGetApp :
          (rest.reverse ++ [x])[rest.length]? =
            ([x] : List α)[rest.length - rest.reverse.length]? :=
        list_getElem?_append_right (by rw [hLen]; exact Nat.le_refl _)
      rw [hEq, hGetApp, hLen, Nat.sub_self, List.length_cons,
        Nat.add_sub_cancel, Nat.sub_self]
      rfl

private theorem list_ext_getElem? {α : Type} :
    ∀ (xs ys : List α),
      xs.length = ys.length →
      (∀ i, i < xs.length → xs[i]? = ys[i]?) →
      xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by nomatch hlen
  | _ :: _, [], hlen, _ => by nomatch hlen
  | x :: xs, y :: ys, hlen, hget => by
    have h0 := hget 0 (by rw [List.length_cons]; exact Nat.zero_lt_succ _)
    have hxy : x = y := by injection h0
    have htail : xs = ys := by
      rw [List.length_cons, List.length_cons] at hlen
      apply list_ext_getElem? xs ys (Nat.succ.inj hlen)
      intro i hi
      exact hget (i + 1) (by
        rw [List.length_cons]
        exact Nat.succ_lt_succ hi)
    rw [hxy, htail]

private theorem list_map_append {α β : Type} (f : α → β) :
    ∀ xs ys : List α, (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: xs, ys => by
    rw [List.cons_append, List.map_cons, List.map_cons, List.cons_append,
      list_map_append f xs ys]

private theorem list_length_map {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (list_length_map f xs)

private theorem list_map_map {α β γ : Type} (f : α → β) (g : β → γ) :
    ∀ xs : List α, (xs.map f).map g = xs.map (fun x => g (f x))
  | [] => rfl
  | _ :: xs => congrArg (List.cons _) (list_map_map f g xs)

private theorem list_flatten_cons {α : Type} (x : List α) (xs : List (List α)) :
    (x :: xs).flatten = x ++ xs.flatten := rfl

private theorem list_flatten_append {α : Type} :
    ∀ xs ys : List (List α), (xs ++ ys).flatten = xs.flatten ++ ys.flatten
  | [], _ => rfl
  | x :: xs, ys => by
    rw [List.cons_append, list_flatten_cons, list_flatten_cons,
      list_flatten_append xs ys, List.append_assoc]

/-! ## Part 1: Bit-Reversal, Leading/Trailing Zeros, Alignment & `Tnum` -/

/-- Structural `@Nat.rec` helper accumulating the lowest `n` reversed bits of
`x : BitVec w`. -/
@[expose] def bvBitreverseAux {w : Nat} (x : BitVec w) (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih =>
      ih + if Anneal.BitVec.getLsbD x (w - 1 - k) then Nat.pow 2 k else 0)
    n

private theorem bvBitreverseAux_zero {w : Nat} (x : BitVec w) :
    bvBitreverseAux x 0 = 0 := rfl

private theorem bvBitreverseAux_succ {w : Nat} (x : BitVec w) (k : Nat) :
    bvBitreverseAux x (k + 1) =
      bvBitreverseAux x k +
        if Anneal.BitVec.getLsbD x (w - 1 - k) then Nat.pow 2 k else 0 :=
  rfl

/-- `bvBitreverseAux x n` fits in `n` bits. -/
theorem bvBitreverseAux_lt {w : Nat} (x : BitVec w) :
    ∀ n : Nat, bvBitreverseAux x n < Nat.pow 2 n
  | 0 => by
    rw [bvBitreverseAux_zero, nat_pow_zero]
    exact Nat.zero_lt_one
  | k + 1 => by
    have ih := bvBitreverseAux_lt x k
    rw [bvBitreverseAux_succ, nat_pow_succ, Nat.mul_two]
    cases Anneal.BitVec.getLsbD x (w - 1 - k) with
    | false =>
      rw [bv_ite_bool_false_eq rfl, Nat.add_zero]
      exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)
    | true =>
      rw [bv_ite_bool_true_eq rfl]
      exact Nat.add_lt_add_right ih (Nat.pow 2 k)

private theorem bvBitreverseAux_testBit {w : Nat} (x : BitVec w) :
    ∀ n i : Nat,
      (bvBitreverseAux x n).testBit i =
        (decide (i < n) && Anneal.BitVec.getLsbD x (w - 1 - i))
  | 0, i => by
    rw [bvBitreverseAux_zero, decide_eq_false (Nat.not_lt_zero i),
      Bool.false_and]
    rw [nat_testBit_eq, nat_zero_div, nat_zero_mod]
    rfl
  | n + 1, i => by
    have ih := bvBitreverseAux_testBit x n i
    have hsLt : bvBitreverseAux x n < Nat.pow 2 n := bvBitreverseAux_lt x n
    rw [bvBitreverseAux_succ]
    cases Nat.lt_trichotomy i n with
    | inl hlt =>
      have hiN1 : i < n + 1 := Nat.lt_succ_of_lt hlt
      rw [decide_eq_true hiN1, Bool.true_and]
      rw [decide_eq_true hlt, Bool.true_and] at ih
      rw [← ih, nat_testBit_eq, nat_testBit_eq]
      cases Anneal.BitVec.getLsbD x (w - 1 - n) with
      | false =>
        rw [bv_ite_bool_false_eq rfl, Nat.add_zero]
      | true =>
        rw [bv_ite_bool_true_eq rfl]
        let d := n - (i + 1)
        have hnEq : n = i + (d + 1) := by
          have h1 : i + 1 ≤ n := hlt
          have h2 := Nat.add_sub_of_le h1
          rw [Nat.add_assoc, Nat.add_comm 1 d] at h2
          exact h2.symm
        have hPow : Nat.pow 2 n = Nat.pow 2 i * (2 * Nat.pow 2 d) := by
          rw [hnEq, nat_pow_add, nat_pow_succ, Nat.mul_comm (Nat.pow 2 d) 2]
        rw [hPow, nat_add_mul_div_left _ _ (nat_two_pow_pos i),
          nat_add_mul_mod_self_left]
    | inr hor =>
      cases hor with
      | inl heq =>
        subst heq
        rw [decide_eq_true (Nat.lt_succ_self i), Bool.true_and, nat_testBit_eq]
        cases hb : Anneal.BitVec.getLsbD x (w - 1 - i) with
        | false =>
          rw [bv_ite_bool_false_eq rfl, Nat.add_zero, nat_div_eq_of_lt hsLt,
            nat_zero_mod]
          rfl
        | true =>
          have hAddDiv :
              Nat.div (bvBitreverseAux x i + Nat.pow 2 i) (Nat.pow 2 i) =
                Nat.div (bvBitreverseAux x i) (Nat.pow 2 i) + 1 := by
            have h1 : bvBitreverseAux x i + Nat.pow 2 i =
                bvBitreverseAux x i + Nat.pow 2 i * 1 := by rw [Nat.mul_one]
            rw [h1]
            exact nat_add_mul_div_left _ _ (nat_two_pow_pos i)
          rw [bv_ite_bool_true_eq rfl, hAddDiv, nat_div_eq_of_lt hsLt,
            Nat.zero_add]
          rfl
      | inr hgt =>
        have hnlt : ¬ (i < n + 1) := Nat.not_lt_of_ge hgt
        rw [decide_eq_false hnlt, Bool.false_and, nat_testBit_eq]
        have hsumLt :
            bvBitreverseAux x n +
              (if Anneal.BitVec.getLsbD x (w - 1 - n) then Nat.pow 2 n else 0) <
              Nat.pow 2 i := by
          have h1 :
              bvBitreverseAux x n +
                (if Anneal.BitVec.getLsbD x (w - 1 - n) then Nat.pow 2 n else 0) <
                Nat.pow 2 (n + 1) := by
            rw [nat_pow_succ, Nat.mul_two]
            cases Anneal.BitVec.getLsbD x (w - 1 - n) with
            | false =>
              rw [bv_ite_bool_false_eq rfl, Nat.add_zero]
              exact Nat.lt_of_lt_of_le hsLt (Nat.le_add_right _ _)
            | true =>
              rw [bv_ite_bool_true_eq rfl]
              exact Nat.add_lt_add_right hsLt (Nat.pow 2 n)
          exact Nat.lt_of_lt_of_le h1
            (Nat.pow_le_pow_right (by decide : 0 < 2) hgt)
        rw [nat_div_eq_of_lt hsumLt, nat_zero_mod]
        rfl

/-- Reverse the `w` bits of `x : BitVec w`. -/
@[expose] def bvBitreverse {w : Nat} (x : BitVec w) : BitVec w :=
  BitVec.ofNatLT (bvBitreverseAux x w) (bvBitreverseAux_lt x w)

/-- Exact `getLsbD` characterization of `bvBitreverse x`. -/
@[simp] theorem getLsbD_bvBitreverse {w : Nat} (x : BitVec w) (i : Nat) :
    Anneal.BitVec.getLsbD (bvBitreverse x) i =
      (decide (i < w) && Anneal.BitVec.getLsbD x (w - 1 - i)) :=
  bvBitreverseAux_testBit x w i

/-- Exact `testBit` characterization of `bvBitreverse x`. -/
theorem testBit_bvBitreverse {w : Nat} (x : BitVec w) (i : Nat) :
    (bvBitreverse x).toNat.testBit i =
      (decide (i < w) && x.toNat.testBit (w - 1 - i)) :=
  getLsbD_bvBitreverse x i

/-- Bit reversal is an involution for every bit width `w`. -/
@[simp] theorem bvBitreverse_bvBitreverse {w : Nat} (x : BitVec w) :
    bvBitreverse (bvBitreverse x) = x := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiRev : w - 1 - i < w := by
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ w' =>
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' i) (Nat.lt_succ_self w')
  have hInv : w - 1 - (w - 1 - i) = i :=
    nat_sub_sub_self (Nat.le_sub_one_of_lt hi)
  rw [getLsbD_bvBitreverse, decide_eq_true hi, Bool.true_and,
    getLsbD_bvBitreverse, decide_eq_true hiRev, Bool.true_and, hInv]

/-- Bit reversal is injective. -/
theorem bvBitreverse_injective {w : Nat} {x y : BitVec w}
    (h : bvBitreverse x = bvBitreverse y) : x = y := by
  rw [← bvBitreverse_bvBitreverse x, ← bvBitreverse_bvBitreverse y, h]

/-- Bit reversal of `0#w` is `0#w`. -/
@[simp] theorem bvBitreverse_zero (w : Nat) :
    bvBitreverse (BitVec.ofNat w 0) = BitVec.ofNat w 0 := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_bvBitreverse, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_zero, Anneal.BitVec.getLsbD_zero]

/-- Bit reversal fixes `allOnes w`. -/
@[simp] theorem bvBitreverse_allOnes (w : Nat) :
    bvBitreverse (Anneal.BitVec.allOnes w) = Anneal.BitVec.allOnes w := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiRev : w - 1 - i < w := by
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ w' =>
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' i) (Nat.lt_succ_self w')
  rw [getLsbD_bvBitreverse, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_allOnes, Anneal.BitVec.getLsbD_allOnes,
    decide_eq_true hiRev, decide_eq_true hi]

/-- `bvBitreverse x = 0#w ↔ x = 0#w`. -/
theorem bvBitreverse_eq_zero_iff {w : Nat} (x : BitVec w) :
    bvBitreverse x = BitVec.ofNat w 0 ↔ x = BitVec.ofNat w 0 := by
  constructor
  · intro h
    apply bvBitreverse_injective
    rw [h, bvBitreverse_zero]
  · intro h
    rw [h, bvBitreverse_zero]

/-- Bit reversal distributes over `Anneal.BitVec.and`. -/
theorem bvBitreverse_and {w : Nat} (x y : BitVec w) :
    bvBitreverse (Anneal.BitVec.and x y) =
      Anneal.BitVec.and (bvBitreverse x) (bvBitreverse y) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_bvBitreverse, Anneal.BitVec.getLsbD_and,
    Anneal.BitVec.getLsbD_and, getLsbD_bvBitreverse, getLsbD_bvBitreverse,
    decide_eq_true hi, Bool.true_and, Bool.true_and, Bool.true_and]

/-- Bit reversal distributes over `Anneal.BitVec.or`. -/
theorem bvBitreverse_or {w : Nat} (x y : BitVec w) :
    bvBitreverse (Anneal.BitVec.or x y) =
      Anneal.BitVec.or (bvBitreverse x) (bvBitreverse y) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_bvBitreverse, Anneal.BitVec.getLsbD_or,
    Anneal.BitVec.getLsbD_or, getLsbD_bvBitreverse, getLsbD_bvBitreverse,
    decide_eq_true hi, Bool.true_and, Bool.true_and, Bool.true_and]

/-- Bit reversal distributes over `Anneal.BitVec.xor`. -/
theorem bvBitreverse_xor {w : Nat} (x y : BitVec w) :
    bvBitreverse (Anneal.BitVec.xor x y) =
      Anneal.BitVec.xor (bvBitreverse x) (bvBitreverse y) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_bvBitreverse, Anneal.BitVec.getLsbD_xor,
    Anneal.BitVec.getLsbD_xor, getLsbD_bvBitreverse, getLsbD_bvBitreverse,
    decide_eq_true hi, Bool.true_and, Bool.true_and, Bool.true_and]

/-- Bit reversal commutes with `Anneal.BitVec.not`. -/
theorem bvBitreverse_not {w : Nat} (x : BitVec w) :
    bvBitreverse (Anneal.BitVec.not x) = Anneal.BitVec.not (bvBitreverse x) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiRev : w - 1 - i < w := by
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ w' =>
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' i) (Nat.lt_succ_self w')
  rw [getLsbD_bvBitreverse, Anneal.BitVec.getLsbD_not_of_lt _ hi,
    Anneal.BitVec.getLsbD_not_of_lt _ hiRev, getLsbD_bvBitreverse,
    decide_eq_true hi, Bool.true_and, Bool.true_and]

/-- Leading zero count of a `w`-bit bitvector (`0 ≤ bvCtlz x ≤ w`), backed by
`Anneal.BitVec.clz`. -/
@[expose] def bvCtlz {w : Nat} (x : BitVec w) : Nat :=
  Anneal.BitVec.clz x

/-- Trailing zero count of a `w`-bit bitvector (`0 ≤ bvCttz x ≤ w`). -/
@[expose] def bvCttz {w : Nat} (x : BitVec w) : Nat :=
  Anneal.BitVec.clz (bvBitreverse x)

/-- Leading zero count never exceeds `w`. -/
theorem bvCtlz_le_width {w : Nat} (x : BitVec w) : bvCtlz x ≤ w :=
  Anneal.BitVec.clz_le x

/-- `bvCtlz (0#w) = w`. -/
@[simp] theorem bvCtlz_zero (w : Nat) : bvCtlz (BitVec.ofNat w 0) = w :=
  (Anneal.BitVec.clz_eq_width_iff (BitVec.ofNat w 0)).2 rfl

/-- `bvCtlz x = w ↔ x = 0#w`. -/
theorem bvCtlz_eq_width_iff {w : Nat} (x : BitVec w) :
    bvCtlz x = w ↔ x = BitVec.ofNat w 0 :=
  Anneal.BitVec.clz_eq_width_iff x

/-- Any nonzero `x : BitVec w` satisfies `bvCtlz x < w`. -/
theorem bvCtlz_lt_of_ne_zero {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) : bvCtlz x < w :=
  Nat.lt_of_le_of_ne (bvCtlz_le_width x)
    (fun heq => hx ((bvCtlz_eq_width_iff x).1 heq))

/-- Every bit at index `i ≥ w - bvCtlz x` is `false`. -/
theorem bvCtlz_high_bits_false {w : Nat} (x : BitVec w) {i : Nat}
    (hi : w - bvCtlz x ≤ i) :
    Anneal.BitVec.getLsbD x i = false :=
  Anneal.BitVec.getLsbD_eq_false_of_ge_sub_clz x hi

/-- Witness bit for `bvCtlz`: for nonzero `x`, bit `w - bvCtlz x - 1` is `true`.
-/
theorem bvCtlz_witness {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) :
    Anneal.BitVec.getLsbD x (w - bvCtlz x - 1) = true :=
  Anneal.BitVec.getLsbD_sub_clz_sub_one hx

/-- Numerical bound: `x.toNat < 2^(w - bvCtlz x)`. -/
theorem bvCtlz_toNat_lt {w : Nat} (x : BitVec w) :
    x.toNat < Nat.pow 2 (w - bvCtlz x) :=
  Anneal.BitVec.toNat_lt_two_pow_sub_clz x

/-- `bvCtlz (bvBitreverse x) = bvCttz x`. -/
@[simp] theorem bvCtlz_bvBitreverse {w : Nat} (x : BitVec w) :
    bvCtlz (bvBitreverse x) = bvCttz x :=
  rfl

/-- `bvCttz (bvBitreverse x) = bvCtlz x`. -/
@[simp] theorem bvCttz_bvBitreverse {w : Nat} (x : BitVec w) :
    bvCttz (bvBitreverse x) = bvCtlz x := by
  unfold bvCttz bvCtlz
  rw [bvBitreverse_bvBitreverse]

/-- Trailing zero count never exceeds `w`. -/
theorem bvCttz_le_width {w : Nat} (x : BitVec w) : bvCttz x ≤ w :=
  Anneal.BitVec.clz_le (bvBitreverse x)

/-- `bvCttz (0#w) = w`. -/
@[simp] theorem bvCttz_zero (w : Nat) : bvCttz (BitVec.ofNat w 0) = w := by
  unfold bvCttz
  rw [bvBitreverse_zero, (Anneal.BitVec.clz_eq_width_iff _).2 rfl]

/-- `bvCttz x = w ↔ x = 0#w`. -/
theorem bvCttz_eq_width_iff {w : Nat} (x : BitVec w) :
    bvCttz x = w ↔ x = BitVec.ofNat w 0 := by
  unfold bvCttz
  rw [Anneal.BitVec.clz_eq_width_iff, bvBitreverse_eq_zero_iff]

/-- Any nonzero `x : BitVec w` satisfies `bvCttz x < w`. -/
theorem bvCttz_lt_of_ne_zero {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) : bvCttz x < w :=
  Nat.lt_of_le_of_ne (bvCttz_le_width x)
    (fun heq => hx ((bvCttz_eq_width_iff x).1 heq))

/-- Every bit strictly below `bvCttz x` is `false`. -/
theorem bvCttz_low_bits_false {w : Nat} (x : BitVec w) {i : Nat}
    (hi : i < bvCttz x) :
    Anneal.BitVec.getLsbD x i = false := by
  have hiW : i < w := Nat.lt_of_lt_of_le hi (bvCttz_le_width x)
  have hjLe : w - bvCttz x ≤ w - 1 - i := by
    rw [Nat.sub_sub, Nat.add_comm 1 i]
    exact Nat.sub_le_sub_left hi w
  have hjLt : w - 1 - i < w := by
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero i hiW)
    | succ w' =>
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' i) (Nat.lt_succ_self w')
  have hInv : w - 1 - (w - 1 - i) = i :=
    nat_sub_sub_self (Nat.le_sub_one_of_lt hiW)
  have hFalse :
      Anneal.BitVec.getLsbD (bvBitreverse x) (w - 1 - i) = false :=
    Anneal.BitVec.getLsbD_eq_false_of_ge_sub_clz (bvBitreverse x) hjLe
  rw [getLsbD_bvBitreverse, decide_eq_true hjLt, Bool.true_and, hInv] at hFalse
  exact hFalse

/-- Witness bit for `bvCttz`: for any nonzero `x : BitVec w`, bit `bvCttz x`
is `true`. -/
theorem bvCttz_witness {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) :
    Anneal.BitVec.getLsbD x (bvCttz x) = true := by
  have hRevNe : bvBitreverse x ≠ BitVec.ofNat w 0 :=
    fun h => hx ((bvBitreverse_eq_zero_iff x).1 h)
  have hWit := Anneal.BitVec.getLsbD_sub_clz_sub_one hRevNe
  change Anneal.BitVec.getLsbD (bvBitreverse x) (w - bvCttz x - 1) = true at hWit
  have hLtW : bvCttz x < w := bvCttz_lt_of_ne_zero hx
  have hjLt : w - bvCttz x - 1 < w := by
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero _ hLtW)
    | succ w' =>
      rw [nat_sub_right_comm, Nat.add_sub_cancel]
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' (bvCttz x)) (Nat.lt_succ_self w')
  have hIdx : w - 1 - (w - bvCttz x - 1) = bvCttz x := by
    rw [nat_sub_right_comm w (bvCttz x) 1]
    exact nat_sub_sub_self (Nat.le_sub_one_of_lt hLtW)
  rw [getLsbD_bvBitreverse, decide_eq_true hjLt, Bool.true_and, hIdx] at hWit
  exact hWit

/-- Uniqueness of `bvCttz`: the least set bit index uniquely determines
`bvCttz x`. -/
theorem bvCttz_eq_of_lowest_bit {w k : Nat} {x : BitVec w} (_hk : k < w)
    (hlow : ∀ i : Nat, i < k → Anneal.BitVec.getLsbD x i = false)
    (hset : Anneal.BitVec.getLsbD x k = true) :
    bvCttz x = k := by
  have hxNe : x ≠ BitVec.ofNat w 0 := by
    intro h0
    rw [h0, Anneal.BitVec.getLsbD_zero] at hset
    nomatch hset
  cases Nat.lt_trichotomy (bvCttz x) k with
  | inl hlt =>
    have hf := hlow (bvCttz x) hlt
    rw [bvCttz_witness hxNe] at hf
    nomatch hf
  | inr hor =>
    cases hor with
    | inl heq => exact heq
    | inr hgt =>
      have hf := bvCttz_low_bits_false x hgt
      rw [hset] at hf
      nomatch hf

/-- Uniqueness of `bvCtlz`: the highest set bit index `k < w` uniquely
determines `bvCtlz x = w - 1 - k`. -/
theorem bvCtlz_eq_of_highest_bit {w k : Nat} {x : BitVec w} (hk : k < w)
    (hhigh : ∀ i : Nat, k < i → Anneal.BitVec.getLsbD x i = false)
    (hset : Anneal.BitVec.getLsbD x k = true) :
    bvCtlz x = w - 1 - k := by
  rw [← bvCttz_bvBitreverse]
  apply bvCttz_eq_of_lowest_bit (k := w - 1 - k)
  · cases w with
    | zero => exact False.elim (Nat.not_lt_zero k hk)
    | succ w' =>
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' k) (Nat.lt_succ_self w')
  · intro i hi
    have hiW : i < w := by
      cases w with
      | zero => exact False.elim (Nat.not_lt_zero k hk)
      | succ w' =>
        have h1 : w' + 1 - 1 - k < w' + 1 :=
          Nat.lt_of_le_of_lt (Nat.sub_le w' k) (Nat.lt_succ_self w')
        exact Nat.lt_trans hi h1
    have hGtK : k < w - 1 - i := by
      have hkLe : k ≤ w - 1 := Nat.le_sub_one_of_lt hk
      apply nat_lt_of_add_lt_add_right (c := i)
      rw [Nat.sub_add_cancel (Nat.le_sub_one_of_lt hiW)]
      have hc : w - 1 - k + k = w - 1 := Nat.sub_add_cancel hkLe
      rw [← hc, Nat.add_comm k i]
      exact Nat.add_lt_add_right hi k
    rw [getLsbD_bvBitreverse, decide_eq_true hiW, Bool.true_and]
    exact hhigh (w - 1 - i) hGtK
  · have hjLt : w - 1 - k < w := by
      cases w with
      | zero => exact False.elim (Nat.not_lt_zero k hk)
      | succ w' =>
        exact Nat.lt_of_le_of_lt (Nat.sub_le w' k) (Nat.lt_succ_self w')
    rw [getLsbD_bvBitreverse, decide_eq_true hjLt, Bool.true_and,
      nat_sub_sub_self (Nat.le_sub_one_of_lt hk)]
    exact hset

/-- Trailing zero count of a single-bit power of two `BitVec.ofNat w (2^k)` for
`k < w`. -/
theorem bvCttz_two_pow {w k : Nat} (hk : k < w) :
    bvCttz (BitVec.ofNat w (Nat.pow 2 k)) = k := by
  apply bvCttz_eq_of_lowest_bit hk
  · intro i hi
    rw [Anneal.BitVec.getLsbD_ofNat, decide_eq_true (Nat.lt_trans hi hk),
      Bool.true_and, nat_testBit_two_pow, decide_eq_false (Nat.ne_of_lt hi)]
  · rw [Anneal.BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and,
      nat_testBit_two_pow, decide_eq_true rfl]

/-- Leading zero count of a single-bit power of two `BitVec.ofNat w (2^k)` for
`k < w`. -/
theorem bvCtlz_two_pow {w k : Nat} (hk : k < w) :
    bvCtlz (BitVec.ofNat w (Nat.pow 2 k)) = w - 1 - k := by
  apply bvCtlz_eq_of_highest_bit hk
  · intro i hi
    cases Nat.lt_or_ge i w with
    | inl hiW =>
      rw [Anneal.BitVec.getLsbD_ofNat, decide_eq_true hiW, Bool.true_and,
        nat_testBit_two_pow, decide_eq_false (Nat.ne_of_gt hi)]
    | inr hiGe =>
      exact Anneal.BitVec.getLsbD_ge _ hiGe
  · rw [Anneal.BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and,
      nat_testBit_two_pow, decide_eq_true rfl]

/-- Trailing zero count alignment mask bridge: `k ≤ bvCttz x` iff masking the
low `k` bits yields zero (for `k ≤ w`). -/
theorem le_bvCttz_iff_and_lowMask_eq_zero {w k : Nat} (x : BitVec w)
    (hk : k ≤ w) :
    k ≤ bvCttz x ↔
      Anneal.BitVec.and x (Anneal.BitVec.lowMask w k) = BitVec.ofNat w 0 := by
  constructor
  · intro hle
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_lowMask hi,
      Anneal.BitVec.getLsbD_zero]
    cases Nat.lt_or_ge i k with
    | inl hlt =>
      rw [bvCttz_low_bits_false x (Nat.lt_of_lt_of_le hlt hle), Bool.false_and]
    | inr hge =>
      rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.and_false]
  · intro hand
    cases Anneal.ClassicalEm.prop_em (x = BitVec.ofNat w 0) with
    | inl hx0 =>
      rw [hx0, bvCttz_zero]
      exact hk
    | inr hxNe =>
      cases Nat.lt_or_ge (bvCttz x) k with
      | inl hlt =>
        have hcttzW : bvCttz x < w := bvCttz_lt_of_ne_zero hxNe
        have hBit := congrArg (fun b => Anneal.BitVec.getLsbD b (bvCttz x)) hand
        rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_lowMask hcttzW,
          bvCttz_witness hxNe, decide_eq_true hlt,
          Anneal.BitVec.getLsbD_zero] at hBit
        nomatch hBit
      | inr hge => exact hge

/-- Equivalence between low-mask zeroing and divisibility by `2^k` for any
`k ≤ w`. -/
theorem and_lowMask_eq_zero_iff_mod_two_pow_eq_zero {w k : Nat}
    (x : BitVec w) (hk : k ≤ w) :
    Anneal.BitVec.and x (Anneal.BitVec.lowMask w k) = BitVec.ofNat w 0 ↔
      Nat.mod x.toNat (Nat.pow 2 k) = 0 := by
  constructor
  · intro hand
    rw [nat_mod_two_pow_eq_zero_iff_testBit]
    intro i hi
    have hiW : i < w := Nat.lt_of_lt_of_le hi hk
    have hBit := congrArg (fun b => Anneal.BitVec.getLsbD b i) hand
    rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_lowMask hiW,
      decide_eq_true hi, Bool.and_true, Anneal.BitVec.getLsbD_zero] at hBit
    exact hBit
  · intro hmod
    exact Anneal.BitVec.mod_two_pow_eq_zero_and_lowMask hmod

/-- Alignment characterization of `bvCttz`: `k ≤ bvCttz x` iff `x.toNat % 2^k =
0` (for `k ≤ w`). -/
theorem le_bvCttz_iff_mod_two_pow_eq_zero {w k : Nat} (x : BitVec w)
    (hk : k ≤ w) :
    k ≤ bvCttz x ↔ Nat.mod x.toNat (Nat.pow 2 k) = 0 :=
  Iff.trans (le_bvCttz_iff_and_lowMask_eq_zero x hk)
    (and_lowMask_eq_zero_iff_mod_two_pow_eq_zero x hk)

private theorem bvCttz_le_of_bit_imp {w : Nat} {a b : BitVec w}
    (himp : ∀ i : Nat, i < w → Anneal.BitVec.getLsbD a i = true →
      Anneal.BitVec.getLsbD b i = true) :
    bvCttz b ≤ bvCttz a := by
  cases Anneal.ClassicalEm.prop_em (a = BitVec.ofNat w 0) with
  | inl ha0 =>
    rw [ha0, bvCttz_zero]
    exact bvCttz_le_width b
  | inr haNe =>
    have haLt : bvCttz a < w := bvCttz_lt_of_ne_zero haNe
    have hbTrue : Anneal.BitVec.getLsbD b (bvCttz a) = true :=
      himp (bvCttz a) haLt (bvCttz_witness haNe)
    cases Nat.lt_or_ge (bvCttz a) (bvCttz b) with
    | inl hlt =>
      have hf := bvCttz_low_bits_false b hlt
      rw [hbTrue] at hf
      nomatch hf
    | inr hge => exact hge

private theorem bvCtlz_le_of_bit_imp {w : Nat} {a b : BitVec w}
    (himp : ∀ i : Nat, i < w → Anneal.BitVec.getLsbD a i = true →
      Anneal.BitVec.getLsbD b i = true) :
    bvCtlz b ≤ bvCtlz a := by
  rw [← bvCttz_bvBitreverse b, ← bvCttz_bvBitreverse a]
  apply bvCttz_le_of_bit_imp
  intro i hi haRev
  have hiRev : w - 1 - i < w := by
    cases w with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ w' =>
      exact Nat.lt_of_le_of_lt (Nat.sub_le w' i) (Nat.lt_succ_self w')
  rw [getLsbD_bvBitreverse, decide_eq_true hi, Bool.true_and] at haRev
  rw [getLsbD_bvBitreverse, decide_eq_true hi, Bool.true_and]
  exact himp (w - 1 - i) hiRev haRev

/-- Tnum lower bound on `bvCttz`: every `x` satisfying `MaskEq m x v` has
`bvCttz (or v m) ≤ bvCttz x`. -/
theorem bvCttz_tnum_lower {w : Nat} {m x v : BitVec w}
    (hm : Anneal.BitVec.MaskEq m x v) :
    bvCttz (Anneal.BitVec.or v m) ≤ bvCttz x := by
  apply bvCttz_le_of_bit_imp
  intro i hi hx
  rw [Anneal.BitVec.getLsbD_or]
  cases hmBit : Anneal.BitVec.getLsbD m i with
  | true => exact Bool.or_true _
  | false =>
    have heq := (Anneal.BitVec.maskEq_iff_getLsbD.1 hm) i hi hmBit
    rw [← heq, hx]
    rfl

/-- Tnum upper bound on `bvCttz`: every `x` satisfying `MaskEq m x v` has
`bvCttz x ≤ bvCttz (and v (not m))`. -/
theorem bvCttz_tnum_upper {w : Nat} {m x v : BitVec w}
    (hm : Anneal.BitVec.MaskEq m x v) :
    bvCttz x ≤ bvCttz (Anneal.BitVec.and v (Anneal.BitVec.not m)) := by
  apply bvCttz_le_of_bit_imp
  intro i hi hvm
  rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_not_of_lt _ hi] at hvm
  have hvTrue : Anneal.BitVec.getLsbD v i = true := bool_and_left hvm
  have hmFalse : Anneal.BitVec.getLsbD m i = false :=
    bool_not_true_eq_false (bool_and_right hvm)
  rw [(Anneal.BitVec.maskEq_iff_getLsbD.1 hm) i hi hmFalse, hvTrue]

/-- Nonzero known-1 tnum implies strict `< w` bound on `bvCttz x`. -/
theorem bvCttz_lt_of_tnum_must_one_ne_zero {w : Nat} {m x v : BitVec w}
    (hm : Anneal.BitVec.MaskEq m x v)
    (hne : Anneal.BitVec.and v (Anneal.BitVec.not m) ≠ BitVec.ofNat w 0) :
    bvCttz x < w :=
  Nat.lt_of_le_of_lt (bvCttz_tnum_upper hm) (bvCttz_lt_of_ne_zero hne)

/-- Tnum lower bound on `bvCtlz`: every `x` satisfying `MaskEq m x v` has
`bvCtlz (or v m) ≤ bvCtlz x`. -/
theorem bvCtlz_tnum_lower {w : Nat} {m x v : BitVec w}
    (hm : Anneal.BitVec.MaskEq m x v) :
    bvCtlz (Anneal.BitVec.or v m) ≤ bvCtlz x := by
  apply bvCtlz_le_of_bit_imp
  intro i hi hx
  rw [Anneal.BitVec.getLsbD_or]
  cases hmBit : Anneal.BitVec.getLsbD m i with
  | true => exact Bool.or_true _
  | false =>
    have heq := (Anneal.BitVec.maskEq_iff_getLsbD.1 hm) i hi hmBit
    rw [← heq, hx]
    rfl

/-- Tnum upper bound on `bvCtlz`: every `x` satisfying `MaskEq m x v` has
`bvCtlz x ≤ bvCtlz (and v (not m))`. -/
theorem bvCtlz_tnum_upper {w : Nat} {m x v : BitVec w}
    (hm : Anneal.BitVec.MaskEq m x v) :
    bvCtlz x ≤ bvCtlz (Anneal.BitVec.and v (Anneal.BitVec.not m)) := by
  apply bvCtlz_le_of_bit_imp
  intro i hi hvm
  rw [Anneal.BitVec.getLsbD_and, Anneal.BitVec.getLsbD_not_of_lt _ hi] at hvm
  have hvTrue : Anneal.BitVec.getLsbD v i = true := bool_and_left hvm
  have hmFalse : Anneal.BitVec.getLsbD m i = false :=
    bool_not_true_eq_false (bool_and_right hvm)
  rw [(Anneal.BitVec.maskEq_iff_getLsbD.1 hm) i hi hmFalse, hvTrue]

/-- Nonzero known-1 tnum implies strict `< w` bound on `bvCtlz x`. -/
theorem bvCtlz_lt_of_tnum_must_one_ne_zero {w : Nat} {m x v : BitVec w}
    (hm : Anneal.BitVec.MaskEq m x v)
    (hne : Anneal.BitVec.and v (Anneal.BitVec.not m) ≠ BitVec.ofNat w 0) :
    bvCtlz x < w :=
  Nat.lt_of_le_of_lt (bvCtlz_tnum_upper hm) (bvCtlz_lt_of_ne_zero hne)

/-- `bvToScalar w s x` equals the zero scalar iff `x = 0`. -/
theorem bvToScalar_eq_zero_iff (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    bvToScalar w s x = bvToScalar w s (BitVec.ofNat (8 * w.byteSize) 0) ↔
      x = BitVec.ofNat (8 * w.byteSize) 0 :=
  ⟨bvToScalar_injective, fun h => congrArg (bvToScalar w s) h⟩

/-- Any nonzero `bvToScalar w s x` has `bvCttz x < w.bitWidth`. -/
theorem bvCttz_lt_bitWidth_of_bvToScalar_ne_zero {w : IntWidth} {s : Bool}
    {x : BitVec (8 * w.byteSize)}
    (hne : bvToScalar w s x ≠
      bvToScalar w s (BitVec.ofNat (8 * w.byteSize) 0)) :
    bvCttz x < w.bitWidth := by
  rw [intWidth_bitWidth_eq_eight_mul]
  exact bvCttz_lt_of_ne_zero
    (fun hx => hne ((bvToScalar_eq_zero_iff w s x).mpr hx))

/-- Any nonzero `bvToScalar w s x` has `bvCtlz x < w.bitWidth`. -/
theorem bvCtlz_lt_bitWidth_of_bvToScalar_ne_zero {w : IntWidth} {s : Bool}
    {x : BitVec (8 * w.byteSize)}
    (hne : bvToScalar w s x ≠
      bvToScalar w s (BitVec.ofNat (8 * w.byteSize) 0)) :
    bvCtlz x < w.bitWidth := by
  rw [intWidth_bitWidth_eq_eight_mul]
  exact bvCtlz_lt_of_ne_zero
    (fun hx => hne ((bvToScalar_eq_zero_iff w s x).mpr hx))

/-- `scalarToBv (bvToScalar w s x)` trailing-zero alignment equivalence across
all `IntWidth` widths (including `.i32`, `.i64`, and `.isize`). -/
theorem le_bvCttz_scalarToBv_iff {w : IntWidth} {k : Nat} (s : Bool)
    (x : BitVec (8 * w.byteSize)) (hk : k ≤ w.bitWidth) :
    k ≤ bvCttz (scalarToBv (bvToScalar w s x)) ↔
      Nat.mod x.toNat (Nat.pow 2 k) = 0 := by
  rw [scalarToBv_bvToScalar]
  rw [intWidth_bitWidth_eq_eight_mul] at hk
  exact le_bvCttz_iff_mod_two_pow_eq_zero x hk

/-! ## Part 2: Population Count, Kernighan Step & `isPow2` Equivalence -/

/-- Structural `@Nat.rec` helper summing the lowest `n` bits of `x : BitVec w`.
-/
@[expose] def bvPopcountAux {w : Nat} (x : BitVec w) (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat)
    0
    (fun k ih => ih + if Anneal.BitVec.getLsbD x k then 1 else 0)
    n

private theorem bvPopcountAux_zero {w : Nat} (x : BitVec w) :
    bvPopcountAux x 0 = 0 := rfl

private theorem bvPopcountAux_succ {w : Nat} (x : BitVec w) (k : Nat) :
    bvPopcountAux x (k + 1) =
      bvPopcountAux x k + if Anneal.BitVec.getLsbD x k then 1 else 0 :=
  rfl

/-- Population count (`count_ones`) of `x : BitVec w`. -/
@[expose] def bvPopcount {w : Nat} (x : BitVec w) : Nat :=
  bvPopcountAux x w

private theorem bvPopcountAux_le {w : Nat} (x : BitVec w) :
    ∀ n : Nat, bvPopcountAux x n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have ih := bvPopcountAux_le x n
    rw [bvPopcountAux_succ]
    cases Anneal.BitVec.getLsbD x n with
    | false =>
      rw [bv_ite_bool_false_eq rfl, Nat.add_zero]
      exact Nat.le_succ_of_le ih
    | true =>
      rw [bv_ite_bool_true_eq rfl]
      exact Nat.succ_le_succ ih

/-- Population count never exceeds the bit width `w`. -/
theorem bvPopcount_le_width {w : Nat} (x : BitVec w) : bvPopcount x ≤ w :=
  bvPopcountAux_le x w

/-- `bvPopcount (0#w) = 0`. -/
@[simp] theorem bvPopcount_zero (w : Nat) :
    bvPopcount (BitVec.ofNat w 0) = 0 := by
  unfold bvPopcount
  have hAux : ∀ n : Nat, bvPopcountAux (BitVec.ofNat w 0) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [bvPopcountAux_succ, Anneal.BitVec.getLsbD_zero,
        bv_ite_bool_false_eq rfl, Nat.add_zero, ih]
  exact hAux w

/-- `bvPopcount (allOnes w) = w`. -/
@[simp] theorem bvPopcount_allOnes (w : Nat) :
    bvPopcount (Anneal.BitVec.allOnes w) = w := by
  unfold bvPopcount
  have hAux : ∀ n : Nat, n ≤ w →
      bvPopcountAux (Anneal.BitVec.allOnes w) n = n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ k ih =>
      have hkW : k < w := hn
      rw [bvPopcountAux_succ, Anneal.BitVec.getLsbD_allOnes,
        decide_eq_true hkW, bv_ite_bool_true_eq rfl, ih (Nat.le_of_lt hkW)]
  exact hAux w (Nat.le_refl w)

private theorem bvPopcountAux_eq_zero_iff {w : Nat} (x : BitVec w) :
    ∀ n : Nat, bvPopcountAux x n = 0 ↔
      ∀ i : Nat, i < n → Anneal.BitVec.getLsbD x i = false
  | 0 => by
    rw [bvPopcountAux_zero]
    constructor
    · intro _ i hi
      exact False.elim (Nat.not_lt_zero i hi)
    · intro _
      rfl
  | n + 1 => by
    have ih := bvPopcountAux_eq_zero_iff x n
    rw [bvPopcountAux_succ]
    cases hb : Anneal.BitVec.getLsbD x n with
    | false =>
      rw [bv_ite_bool_false_eq rfl, Nat.add_zero, ih]
      constructor
      · intro hlow i hi
        cases Nat.lt_or_ge i n with
        | inl hlt => exact hlow i hlt
        | inr hge =>
          have heq : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
          rw [heq]
          exact hb
      · intro hall i hi
        exact hall i (Nat.lt_succ_of_lt hi)
    | true =>
      rw [bv_ite_bool_true_eq rfl]
      constructor
      · intro h
        nomatch h
      · intro hall
        have hf := hall n (Nat.lt_succ_self n)
        rw [hb] at hf
        nomatch hf

/-- `bvPopcount x = 0 ↔ x = 0#w`. -/
theorem bvPopcount_eq_zero_iff {w : Nat} (x : BitVec w) :
    bvPopcount x = 0 ↔ x = BitVec.ofNat w 0 := by
  unfold bvPopcount
  rw [bvPopcountAux_eq_zero_iff]
  constructor
  · intro hall
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_zero]
    exact hall i hi
  · intro hx i _
    rw [hx, Anneal.BitVec.getLsbD_zero]

/-- Any nonzero `x : BitVec w` has positive population count. -/
theorem bvPopcount_pos_of_ne_zero {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) : 0 < bvPopcount x :=
  Nat.pos_of_ne_zero (fun h0 => hx ((bvPopcount_eq_zero_iff x).1 h0))

/-- Complement sum law: `bvPopcount (not x) + bvPopcount x = w`. -/
theorem bvPopcount_not_add {w : Nat} (x : BitVec w) :
    bvPopcount (Anneal.BitVec.not x) + bvPopcount x = w := by
  unfold bvPopcount
  have hAux : ∀ n : Nat, n ≤ w →
      bvPopcountAux (Anneal.BitVec.not x) n + bvPopcountAux x n = n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ k ih =>
      have hkW : k < w := hn
      rw [bvPopcountAux_succ, bvPopcountAux_succ,
        Anneal.BitVec.getLsbD_not_of_lt _ hkW,
        add_four_rearrange, ih (Nat.le_of_lt hkW)]
      cases Anneal.BitVec.getLsbD x k <;> rfl
  exact hAux w (Nat.le_refl w)

/-- Complement law: `bvPopcount (not x) = w - bvPopcount x`. -/
theorem bvPopcount_not {w : Nat} (x : BitVec w) :
    bvPopcount (Anneal.BitVec.not x) = w - bvPopcount x := by
  have h := congrArg (fun z => z - bvPopcount x) (bvPopcount_not_add x)
  rw [Nat.add_sub_cancel] at h
  exact h

/-- Inclusion-exclusion law for bitwise `or` and `and`. -/
theorem bvPopcount_or_add_and {w : Nat} (x y : BitVec w) :
    bvPopcount (Anneal.BitVec.or x y) + bvPopcount (Anneal.BitVec.and x y) =
      bvPopcount x + bvPopcount y := by
  unfold bvPopcount
  have hAux : ∀ n : Nat,
      bvPopcountAux (Anneal.BitVec.or x y) n +
          bvPopcountAux (Anneal.BitVec.and x y) n =
        bvPopcountAux x n + bvPopcountAux y n := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [bvPopcountAux_succ, bvPopcountAux_succ, bvPopcountAux_succ,
        bvPopcountAux_succ, Anneal.BitVec.getLsbD_or,
        Anneal.BitVec.getLsbD_and,
        add_four_rearrange (bvPopcountAux (Anneal.BitVec.or x y) k) _
          (bvPopcountAux (Anneal.BitVec.and x y) k) _,
        add_four_rearrange (bvPopcountAux x k) _ (bvPopcountAux y k) _, ih]
      cases Anneal.BitVec.getLsbD x k <;>
        cases Anneal.BitVec.getLsbD y k <;>
        rfl
  exact hAux w

/-- Disjoint bitwise OR additivity: `and x y = 0 → popcount (or x y) = popcount
x + popcount y`. -/
theorem bvPopcount_or_of_disjoint {w : Nat} {x y : BitVec w}
    (hd : Anneal.BitVec.and x y = BitVec.ofNat w 0) :
    bvPopcount (Anneal.BitVec.or x y) = bvPopcount x + bvPopcount y := by
  have h := bvPopcount_or_add_and x y
  rw [hd, bvPopcount_zero, Nat.add_zero] at h
  exact h

private theorem bvPopcountAux_lowMask {w k : Nat} :
    ∀ n : Nat, n ≤ w →
      bvPopcountAux (Anneal.BitVec.lowMask w k) n =
        if k ≤ n then k else n
  | 0, _ => by
    rw [bvPopcountAux_zero]
    cases k with
    | zero => rfl
    | succ k' =>
      rw [ite_false_of (Nat.not_succ_le_zero k')]
  | n + 1, hle => by
    have hnW : n < w := hle
    have ih := bvPopcountAux_lowMask (w := w) (k := k) n (Nat.le_of_lt hnW)
    rw [bvPopcountAux_succ, Anneal.BitVec.getLsbD_lowMask hnW, ih]
    cases Nat.lt_trichotomy n k with
    | inl hlt =>
      have hnNotGe : ¬ (k ≤ n) := Nat.not_le_of_gt hlt
      rw [ite_false_of hnNotGe, decide_eq_true hlt, bv_ite_bool_true_eq rfl]
      cases Nat.lt_or_ge (n + 1) k with
      | inl hlt1 => rw [ite_false_of (Nat.not_le_of_gt hlt1)]
      | inr hge1 =>
        have hkEq : k = n + 1 := Nat.le_antisymm hge1 hlt
        rw [ite_true_of hge1, hkEq]
    | inr hor =>
      cases hor with
      | inl heq =>
        rw [heq]
        rw [ite_true_of (Nat.le_refl k),
          ite_true_of (Nat.le_succ k),
          decide_eq_false (Nat.lt_irrefl k), bv_ite_bool_false_eq rfl,
          Nat.add_zero]
      | inr hgt =>
        have hkn : k ≤ n := Nat.le_of_lt hgt
        rw [ite_true_of hkn, ite_true_of (Nat.le_succ_of_le hkn),
          decide_eq_false (Nat.not_lt_of_ge hkn), bv_ite_bool_false_eq rfl,
          Nat.add_zero]

/-- Population count of `lowMask w k` equals `min k w`. -/
theorem bvPopcount_lowMask (w k : Nat) :
    bvPopcount (Anneal.BitVec.lowMask w k) = if k ≤ w then k else w :=
  bvPopcountAux_lowMask w (Nat.le_refl w)

/-- When `k ≤ w`, `bvPopcount (lowMask w k) = k`. -/
theorem bvPopcount_lowMask_of_le {w k : Nat} (hk : k ≤ w) :
    bvPopcount (Anneal.BitVec.lowMask w k) = k := by
  rw [bvPopcount_lowMask, ite_true_of hk]

/-- Any single-bit power of two `BitVec.ofNat w (2^k)` (`k < w`) has population
count `1`. -/
theorem bvPopcount_two_pow {w k : Nat} (hk : k < w) :
    bvPopcount (BitVec.ofNat w (Nat.pow 2 k)) = 1 := by
  unfold bvPopcount
  have hAux : ∀ n : Nat, n ≤ w →
      bvPopcountAux (BitVec.ofNat w (Nat.pow 2 k)) n =
        if k < n then 1 else 0 := by
    intro n hn
    induction n with
    | zero => rfl
    | succ m ih =>
      have hmW : m < w := hn
      rw [bvPopcountAux_succ, Anneal.BitVec.getLsbD_ofNat, decide_eq_true hmW,
        Bool.true_and, nat_testBit_two_pow, ih (Nat.le_of_lt hmW)]
      cases Nat.lt_trichotomy m k with
      | inl hlt =>
        have hnot1 : ¬ (k < m) :=
          fun h => Nat.not_lt_of_ge (Nat.le_of_lt hlt) h
        have hnot2 : ¬ (k < m + 1) := Nat.not_lt_of_ge hlt
        rw [ite_false_of hnot1, decide_eq_false (Nat.ne_of_lt hlt),
          bv_ite_bool_false_eq rfl, ite_false_of hnot2]
      | inr hor =>
        cases hor with
        | inl heq =>
          subst heq
          rw [ite_false_of (Nat.lt_irrefl m), decide_eq_true rfl,
            bv_ite_bool_true_eq rfl, ite_true_of (Nat.lt_succ_self m)]
        | inr hgt =>
          rw [ite_true_of hgt, ite_true_of (Nat.lt_succ_of_lt hgt),
            decide_eq_false (Nat.ne_of_gt hgt), bv_ite_bool_false_eq rfl,
            Nat.add_zero]
  rw [hAux w (Nat.le_refl w), ite_true_of hk]

private def sumShift (f : Nat → Nat) (off n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun k ih => ih + f (off + k)) n

private theorem sumShift_zero (f : Nat → Nat) (off : Nat) :
    sumShift f off 0 = 0 := rfl

private theorem sumShift_succ (f : Nat → Nat) (off n : Nat) :
    sumShift f off (n + 1) = sumShift f off n + f (off + n) := rfl

private theorem sumShift_succ_zero (f : Nat → Nat) (off : Nat) :
    ∀ n : Nat, sumShift f off (n + 1) = f off + sumShift f (off + 1) n
  | 0 => by
    rw [sumShift_succ, sumShift_zero, sumShift_zero, Nat.add_zero,
      Nat.zero_add, Nat.add_zero]
  | n + 1 => by
    rw [sumShift_succ, sumShift_succ_zero f off n, sumShift_succ,
      Nat.add_assoc off 1 n, Nat.add_comm 1 n, Nat.add_assoc]

private theorem sumShift_rev_eq (f : Nat → Nat) :
    ∀ (n off : Nat),
      sumShift (fun k => f (off + n - 1 - k)) 0 n = sumShift f off n
  | 0, off => by
    rw [sumShift_zero, sumShift_zero]
  | n + 1, off => by
    have hFun : (fun k => f (off + (n + 1) - 1 - k)) =
        (fun k => f ((off + 1) + n - 1 - k)) := by
      funext k
      have hBase : off + (n + 1) - 1 = (off + 1) + n - 1 := by
        rw [← Nat.add_assoc off n 1, Nat.add_sub_cancel,
          Nat.add_comm (off + 1) n, ← Nat.add_assoc n off 1,
          Nat.add_sub_cancel, Nat.add_comm n off]
      rw [hBase]
    have hLast : off + (n + 1) - 1 - (0 + n) = off := by
      rw [Nat.zero_add, ← Nat.add_assoc off n 1, Nat.add_sub_cancel,
        Nat.add_sub_cancel]
    rw [sumShift_succ, hLast, hFun, sumShift_rev_eq f n (off + 1),
      Nat.add_comm, ← sumShift_succ_zero]

private theorem bvPopcountAux_eq_sumShift {w : Nat} (x : BitVec w) :
    ∀ n : Nat, bvPopcountAux x n =
      sumShift (fun k => if Anneal.BitVec.getLsbD x k then 1 else 0) 0 n
  | 0 => rfl
  | n + 1 => by
    rw [bvPopcountAux_succ, sumShift_succ, Nat.zero_add,
      bvPopcountAux_eq_sumShift x n]

private theorem sumShift_congr {f g : Nat → Nat} {off : Nat} :
    ∀ n : Nat, (∀ k : Nat, k < n → f (off + k) = g (off + k)) →
      sumShift f off n = sumShift g off n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumShift_succ, sumShift_succ,
      sumShift_congr n (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      h n (Nat.lt_succ_self n)]

/-- Bit reversal preserves population count. -/
@[simp] theorem bvPopcount_bvBitreverse {w : Nat} (x : BitVec w) :
    bvPopcount (bvBitreverse x) = bvPopcount x := by
  unfold bvPopcount
  rw [bvPopcountAux_eq_sumShift, bvPopcountAux_eq_sumShift]
  have hCongr :
      sumShift (fun k =>
          if Anneal.BitVec.getLsbD (bvBitreverse x) k then 1 else 0) 0 w =
        sumShift (fun k =>
          if Anneal.BitVec.getLsbD x (0 + w - 1 - k) then 1 else 0) 0 w := by
    apply sumShift_congr w
    intro k hk
    rw [Nat.zero_add k, Nat.zero_add w, getLsbD_bvBitreverse,
      decide_eq_true hk, Bool.true_and]
  rw [hCongr]
  exact sumShift_rev_eq (fun k => if Anneal.BitVec.getLsbD x k then 1 else 0) w 0

/-- Exact bit characterization of Brian Kernighan's bit-clearing step
`x &&& (x - 1)` for any nonzero `x : BitVec w`. -/
theorem getLsbD_and_sub_one {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) (i : Nat) :
    Anneal.BitVec.getLsbD
        (Anneal.BitVec.and x (x - BitVec.ofNat w 1)) i =
      if i == bvCttz x then false else Anneal.BitVec.getLsbD x i := by
  let k := bvCttz x
  have hkW : k < w := bvCttz_lt_of_ne_zero hx
  have hlow : ∀ j : Nat, j < k → Anneal.BitVec.getLsbD x j = false :=
    fun _ hj => bvCttz_low_bits_false x hj
  have hwit : Anneal.BitVec.getLsbD x k = true := bvCttz_witness hx
  have hmodK : Nat.mod x.toNat (Nat.pow 2 k) = 0 :=
    (nat_mod_two_pow_eq_zero_iff_testBit x.toNat k).2 hlow
  have hdivK_odd : Nat.mod (Nat.div x.toNat (Nat.pow 2 k)) 2 = 1 := by
    have hbit : x.toNat.testBit k = true := hwit
    rw [nat_testBit_eq] at hbit
    exact of_decide_eq_true hbit
  let q := Nat.div x.toNat (Nat.pow 2 (k + 1))
  have hxEq : x.toNat = Nat.pow 2 (k + 1) * q + Nat.pow 2 k := by
    have h1 : x.toNat = Nat.pow 2 k * Nat.div x.toNat (Nat.pow 2 k) := by
      have hda := (nat_div_add_mod x.toNat (Nat.pow 2 k)).symm
      rw [hmodK, Nat.add_zero] at hda
      exact hda
    have hqDef : q = Nat.div (Nat.div x.toNat (Nat.pow 2 k)) 2 := by
      unfold q
      rw [nat_pow_succ, ← nat_div_div_eq_div_mul]
    have h2 : Nat.div x.toNat (Nat.pow 2 k) = 2 * q + 1 := by
      have hda := (nat_div_add_mod (Nat.div x.toNat (Nat.pow 2 k)) 2).symm
      rw [← hqDef, hdivK_odd] at hda
      exact hda
    rw [h1, h2, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← nat_pow_succ]
  have h1ltW : 1 < Nat.pow 2 w := by
    have hwPos : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le k) hkW
    have h1le : 1 ≤ Nat.pow 2 (w - 1) := nat_two_pow_pos (w - 1)
    rw [nat_two_pow_split hwPos]
    exact Nat.lt_of_lt_of_le (by decide : 1 < 1 + 1)
      (Nat.add_le_add h1le h1le)
  have h1leX : BitVec.ofNat w 1 ≤ x := by
    change (BitVec.ofNat w 1).toNat ≤ x.toNat
    rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt h1ltW, hxEq]
    exact Nat.le_trans (nat_two_pow_pos k) (Nat.le_add_left _ _)
  have hsubEq : (x - BitVec.ofNat w 1).toNat =
      Nat.pow 2 (k + 1) * q + (Nat.pow 2 k - 1) := by
    rw [Anneal.BitVec.toNat_sub_of_le h1leX, Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt h1ltW, hxEq]
    have hpos : 0 < Nat.pow 2 k := nat_two_pow_pos k
    exact Nat.add_sub_assoc hpos _
  rw [Anneal.BitVec.getLsbD_and]
  cases Nat.lt_trichotomy i k with
  | inl hlt =>
    have hne : (i == k) = false := decide_eq_false (Nat.ne_of_lt hlt)
    rw [bv_ite_cond_false hne]
    rw [hlow i hlt, Bool.false_and]
  | inr hor =>
    cases hor with
    | inl heq =>
      subst heq
      rw [beq_self_eq_true, bv_ite_cond_true, hwit, Bool.true_and]
      change (x - BitVec.ofNat w 1).toNat.testBit k = false
      rw [nat_testBit_eq]
      have hpowK1 : Nat.pow 2 (k + 1) = Nat.pow 2 k * 2 := nat_pow_succ 2 k
      have hdivSub :
          Nat.div (x - BitVec.ofNat w 1).toNat (Nat.pow 2 k) = 2 * q := by
        rw [hsubEq, hpowK1, Nat.mul_assoc,
          Nat.add_comm (Nat.pow 2 k * (2 * q)) (Nat.pow 2 k - 1),
          nat_add_mul_div_left _ _ (nat_two_pow_pos k),
          nat_div_eq_of_lt (Nat.sub_lt (nat_two_pow_pos k) Nat.one_pos),
          Nat.zero_add]
      rw [hdivSub, nat_mul_mod_right]
      rfl
    | inr hgt =>
      have hne : (i == k) = false := decide_eq_false (Nat.ne_of_gt hgt)
      rw [bv_ite_cond_false hne]
      let d := i - (k + 1)
      have hiEq : i = (k + 1) + d := (Nat.add_sub_of_le hgt).symm
      have hDivX : Nat.div x.toNat (Nat.pow 2 (k + 1)) = q := by
        rw [hxEq, Nat.add_comm, nat_add_mul_div_left _ _ (nat_two_pow_pos _),
          nat_div_eq_of_lt (by
            rw [nat_pow_succ, Nat.mul_two]
            exact Nat.lt_add_of_pos_right (nat_two_pow_pos k)),
          Nat.zero_add]
      have hDivSub :
          Nat.div (x - BitVec.ofNat w 1).toNat (Nat.pow 2 (k + 1)) = q := by
        rw [hsubEq, Nat.add_comm, nat_add_mul_div_left _ _ (nat_two_pow_pos _),
          nat_div_eq_of_lt (by
            have h1 : Nat.pow 2 k - 1 < Nat.pow 2 k :=
              Nat.sub_lt (nat_two_pow_pos k) Nat.one_pos
            rw [nat_pow_succ, Nat.mul_two]
            exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)),
          Nat.zero_add]
      have hSubSame :
          Anneal.BitVec.getLsbD (x - BitVec.ofNat w 1) i =
            Anneal.BitVec.getLsbD x i := by
        change (x - BitVec.ofNat w 1).toNat.testBit i = x.toNat.testBit i
        rw [hiEq, nat_testBit_add, nat_testBit_add, hDivX, hDivSub]
      rw [hSubSame, Bool.and_self]

private theorem bvPopcountAux_drop_bit {w k : Nat} {x y : BitVec w} :
    ∀ n : Nat, k < n →
      Anneal.BitVec.getLsbD x k = true →
      Anneal.BitVec.getLsbD y k = false →
      (∀ i : Nat, i < n → i ≠ k →
        Anneal.BitVec.getLsbD y i = Anneal.BitVec.getLsbD x i) →
      bvPopcountAux y n + 1 = bvPopcountAux x n
  | 0, hk, _, _, _ => False.elim (Nat.not_lt_zero k hk)
  | n + 1, hk, hxk, hyk, hrest => by
    rw [bvPopcountAux_succ, bvPopcountAux_succ]
    cases Nat.lt_or_ge k n with
    | inl hlt =>
      have hne : n ≠ k := Nat.ne_of_gt hlt
      have heqN : Anneal.BitVec.getLsbD y n = Anneal.BitVec.getLsbD x n :=
        hrest n (Nat.lt_succ_self n) hne
      have ih := bvPopcountAux_drop_bit n hlt hxk hyk
        (fun i hi hink => hrest i (Nat.lt_succ_of_lt hi) hink)
      rw [heqN, Nat.add_right_comm, ih]
    | inr hge =>
      have hkn : k = n := Nat.le_antisymm (Nat.le_of_lt_succ hk) hge
      subst hkn
      have hauxEq : ∀ m : Nat, m ≤ k →
          (∀ i : Nat, i < m →
            Anneal.BitVec.getLsbD y i = Anneal.BitVec.getLsbD x i) →
          bvPopcountAux y m = bvPopcountAux x m := by
        intro m
        induction m with
        | zero => intro _ _; rfl
        | succ m' ihM =>
          intro hleM hm
          rw [bvPopcountAux_succ, bvPopcountAux_succ,
            ihM (Nat.le_of_lt hleM) (fun i hi => hm i (Nat.lt_succ_of_lt hi)),
            hm m' (Nat.lt_succ_self m')]
      have heqBelow := hauxEq k (Nat.le_refl k)
        (fun i hi => hrest i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi))
      rw [heqBelow, hyk, hxk, bv_ite_bool_false_eq rfl, bv_ite_bool_true_eq rfl,
        Nat.add_zero]

/-- Brian Kernighan's bit-clearing identity: clearing the lowest set bit via
`x &&& (x - 1)` reduces `bvPopcount` by exactly `1`. -/
theorem bvPopcount_kernighan_step {w : Nat} {x : BitVec w}
    (hx : x ≠ BitVec.ofNat w 0) :
    bvPopcount (Anneal.BitVec.and x (x - BitVec.ofNat w 1)) + 1 =
      bvPopcount x := by
  unfold bvPopcount
  have hkW : bvCttz x < w := bvCttz_lt_of_ne_zero hx
  apply bvPopcountAux_drop_bit (k := bvCttz x) w hkW (bvCttz_witness hx)
  · rw [getLsbD_and_sub_one hx, beq_self_eq_true]
    rfl
  · intro i _ hne
    rw [getLsbD_and_sub_one hx]
    have hBeq : (i == bvCttz x) = false := decide_eq_false hne
    rw [hBeq]
    rfl

/-- Boolean predicate checking whether `x : BitVec w` is an exact power of two
(`x ≠ 0 ∧ x &&& (x - 1) = 0`). -/
@[expose] def isPow2Bv {w : Nat} (x : BitVec w) : Bool :=
  (x != BitVec.ofNat w 0) &&
    (Anneal.BitVec.and x (x - BitVec.ofNat w 1) == BitVec.ofNat w 0)

/-- Power-of-two equivalence: `bvPopcount x = 1` iff `x ≠ 0` and
`and x (x - 1) = 0`. -/
theorem bvPopcount_eq_one_iff_and_sub_one_eq_zero {w : Nat} (x : BitVec w) :
    bvPopcount x = 1 ↔
      (x ≠ BitVec.ofNat w 0 ∧
        Anneal.BitVec.and x (x - BitVec.ofNat w 1) = BitVec.ofNat w 0) := by
  constructor
  · intro hp1
    have hxNe : x ≠ BitVec.ofNat w 0 := by
      intro h0
      rw [h0, bvPopcount_zero] at hp1
      nomatch hp1
    have hStep := bvPopcount_kernighan_step hxNe
    rw [hp1] at hStep
    have hPop0 : bvPopcount (Anneal.BitVec.and x (x - BitVec.ofNat w 1)) = 0 :=
      Nat.succ.inj hStep
    exact ⟨hxNe, (bvPopcount_eq_zero_iff _).1 hPop0⟩
  · intro ⟨hxNe, hand0⟩
    have hStep := bvPopcount_kernighan_step hxNe
    rw [hand0, bvPopcount_zero, Nat.zero_add] at hStep
    exact hStep.symm

/-- Exact characterization of `bvPopcount x = 1`: `x` equals `BitVec.ofNat w
(Nat.pow 2 k)` for some `k < w`. -/
theorem bvPopcount_eq_one_iff_exists_two_pow {w : Nat} (x : BitVec w) :
    bvPopcount x = 1 ↔
      ∃ k : Nat, k < w ∧ x = BitVec.ofNat w (Nat.pow 2 k) := by
  constructor
  · intro hp1
    have ⟨hxNe, hand0⟩ := (bvPopcount_eq_one_iff_and_sub_one_eq_zero x).1 hp1
    refine ⟨bvCttz x, bvCttz_lt_of_ne_zero hxNe, ?_⟩
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Anneal.BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and,
      nat_testBit_two_pow]
    cases Anneal.ClassicalEm.prop_em (i = bvCttz x) with
    | inl heq =>
      rw [heq, decide_eq_true rfl, bvCttz_witness hxNe]
    | inr hne =>
      rw [decide_eq_false hne]
      have hBit := congrArg (fun b => Anneal.BitVec.getLsbD b i) hand0
      rw [getLsbD_and_sub_one hxNe, Anneal.BitVec.getLsbD_zero] at hBit
      have hBeq : (i == bvCttz x) = false := decide_eq_false hne
      rw [hBeq] at hBit
      exact hBit
  · intro ⟨k, hk, hxEq⟩
    rw [hxEq]
    exact bvPopcount_two_pow hk

/-- `isPow2Bv x = true ↔ bvPopcount x = 1`. -/
theorem isPow2Bv_eq_true_iff_bvPopcount_eq_one {w : Nat} (x : BitVec w) :
    isPow2Bv x = true ↔ bvPopcount x = 1 := by
  unfold isPow2Bv
  rw [bool_and_iff, bvPopcount_eq_one_iff_and_sub_one_eq_zero]
  constructor
  · intro ⟨hne, hand⟩
    exact ⟨bne_iff_ne.mp hne, of_decide_eq_true hand⟩
  · intro ⟨hne, hand⟩
    exact ⟨bne_iff_ne.mpr hne, decide_eq_true hand⟩

/-- `isPow2Bv x = true ↔ ∃ k < w, x = BitVec.ofNat w (2^k)`. -/
theorem isPow2Bv_eq_true_iff_exists_two_pow {w : Nat} (x : BitVec w) :
    isPow2Bv x = true ↔
      ∃ k : Nat, k < w ∧ x = BitVec.ofNat w (Nat.pow 2 k) :=
  Iff.trans (isPow2Bv_eq_true_iff_bvPopcount_eq_one x)
    (bvPopcount_eq_one_iff_exists_two_pow x)

/-- Any single-bit value (`bvPopcount x = 1`) satisfies `bvCttz x + bvCtlz x + 1
= w`. -/
theorem bvCttz_add_bvCtlz_eq_of_isPow2 {w : Nat} {x : BitVec w}
    (hp : bvPopcount x = 1) :
    bvCttz x + bvCtlz x + 1 = w := by
  let ⟨k, hk, hxEq⟩ := (bvPopcount_eq_one_iff_exists_two_pow x).1 hp
  subst hxEq
  rw [bvCttz_two_pow hk, bvCtlz_two_pow hk, Nat.add_assoc,
    Nat.add_comm (w - 1 - k) 1]
  have hkLe : k ≤ w - 1 := Nat.le_sub_one_of_lt hk
  have h1 : k + (1 + (w - 1 - k)) = w - 1 + 1 := by
    rw [← Nat.add_assoc, Nat.add_comm k 1, Nat.add_assoc 1 k (w - 1 - k),
      Nat.add_sub_of_le hkLe, Nat.add_comm]
  rw [h1]
  exact Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)

/-! ## Part 3: Byte-Swap (`bvBswap`) & Endian Memory Round-Trips -/

/-- Reverse byte order of an `IntWidth`-indexed bitvector, backed by
`Anneal.BitVecArith.bswapBytes`. -/
@[expose] noncomputable def bvBswap (w : IntWidth) (x : BitVec (8 * w.byteSize)) :
    BitVec (8 * w.byteSize) :=
  Anneal.BitVecArith.bswapBytes w.byteSize x

/-- Byte swap is an involution across every `IntWidth`. -/
@[simp] theorem bvBswap_bvBswap (w : IntWidth) (x : BitVec (8 * w.byteSize)) :
    bvBswap w (bvBswap w x) = x :=
  Anneal.BitVecArith.bswapBytes_bswapBytes w.byteSize x

/-- Byte swap is injective across every `IntWidth`. -/
theorem bvBswap_injective {w : IntWidth} {x y : BitVec (8 * w.byteSize)}
    (h : bvBswap w x = bvBswap w y) : x = y :=
  Anneal.BitVecArith.bswapBytes_injective h

/-- Byte swap of `0` is `0` for every byte count `n`. -/
@[simp] theorem bswapBytes_zero (n : Nat) :
    Anneal.BitVecArith.bswapBytes n (BitVec.ofNat (8 * n) 0) =
      BitVec.ofNat (8 * n) 0 := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Anneal.BitVecArith.getLsbD_bswapBytes, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_zero, Anneal.BitVec.getLsbD_zero]

/-- Byte swap fixes `allOnes (8 * n)` for every byte count `n`. -/
@[simp] theorem bswapBytes_allOnes (n : Nat) :
    Anneal.BitVecArith.bswapBytes n (Anneal.BitVec.allOnes (8 * n)) =
      Anneal.BitVec.allOnes (8 * n) := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  have h8 : 0 < 8 := by decide
  have hdivLt : Nat.div i 8 < n := by
    rw [nat_div_lt_iff_lt_mul h8, Nat.mul_comm n 8]
    exact hi
  have hrevLt : n - 1 - Nat.div i 8 < n :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hdivLt) Nat.one_pos)
  have hjLt : Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8) < 8 * n := by
    have h1 : Nat.mod i 8 + 8 * (n - 1 - Nat.div i 8) <
        8 + 8 * (n - 1 - Nat.div i 8) :=
      Nat.add_lt_add_right (Nat.mod_lt i h8) _
    have h2 : 8 + 8 * (n - 1 - Nat.div i 8) =
        8 * ((n - 1 - Nat.div i 8) + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 8 hrevLt)
  rw [Anneal.BitVecArith.getLsbD_bswapBytes, decide_eq_true hi, Bool.true_and,
    Anneal.BitVec.getLsbD_allOnes, Anneal.BitVec.getLsbD_allOnes,
    decide_eq_true hjLt, decide_eq_true hi]

/-- Single-byte byte swap (`1` byte / `.i8`) is the identity. -/
@[simp] theorem bswapBytes_one (x : BitVec (8 * 1)) :
    Anneal.BitVecArith.bswapBytes 1 x = x := by
  apply Anneal.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Anneal.BitVecArith.getLsbD_bswapBytes, decide_eq_true hi, Bool.true_and]
  have hdiv0 : Nat.div i 8 = 0 := nat_div_eq_of_lt hi
  have hmod : Nat.mod i 8 = i := nat_mod_eq_of_lt hi
  rw [hdiv0, Nat.sub_self, Nat.mul_zero, Nat.add_zero, hmod]

/-- `.i8` byte swap is the identity. -/
@[simp] theorem bvBswap_i8 (x : BitVec (8 * IntWidth.i8.byteSize)) :
    bvBswap .i8 x = x :=
  bswapBytes_one x

/-- Exact byte-list reversal bridge: little-endian encoding of `bswapBytes n x`
equals big-endian encoding `(toLeBytes n (toLeWidth x)).reverse = toBeBytes n
(toLeWidth x)`. -/
theorem toLeBytes_toLeWidth_bswapBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.LeBytes.toLeBytes n (toLeWidth (Anneal.BitVecArith.bswapBytes n x)) =
      (Anneal.LeBytes.toLeBytes n (toLeWidth x)).reverse := by
  apply list_ext_getElem?
  · rw [Anneal.LeBytes.toLeBytes_length, list_length_reverse,
      Anneal.LeBytes.toLeBytes_length]
  · intro i hi
    rw [Anneal.LeBytes.toLeBytes_length] at hi
    rw [list_getElem?_reverse _ i (by rw [Anneal.LeBytes.toLeBytes_length]; exact hi),
      Anneal.LeBytes.toLeBytes_length]
    have hRevLt : n - 1 - i < n := by
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i hi)
      | succ n' =>
        exact Nat.lt_of_le_of_lt (Nat.sub_le n' i) (Nat.lt_succ_self n')
    unfold Anneal.LeBytes.toLeBytes
    rw [toNat_toLeWidth, toNat_toLeWidth,
      Anneal.LeBytes.toLeBytes_getElem? n _ i hi,
      Anneal.LeBytes.toLeBytes_getElem? n _ (n - 1 - i) hRevLt]
    apply congrArg some
    apply Anneal.BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [Anneal.BitVec.getLsbD_ofNat, Anneal.BitVec.getLsbD_ofNat,
      decide_eq_true hj, Bool.true_and, Bool.true_and]
    change (Nat.div (Anneal.BitVecArith.bswapBytes n x).toNat
        (Nat.pow 2 (8 * i))).testBit j =
      (Nat.div x.toNat (Nat.pow 2 (8 * (n - 1 - i)))).testBit j
    rw [← nat_testBit_add, ← nat_testBit_add]
    change Anneal.BitVec.getLsbD (Anneal.BitVecArith.bswapBytes n x) (8 * i + j) =
      Anneal.BitVec.getLsbD x (8 * (n - 1 - i) + j)
    have hBound : 8 * i + j < 8 * n := by
      have h1 : 8 * i + j < 8 * i + 8 := Nat.add_lt_add_left hj (8 * i)
      have h2 : 8 * i + 8 = 8 * (i + 1) := (Nat.mul_succ 8 i).symm
      rw [h2] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 8 hi)
    have h8pos : 0 < 8 := by decide
    have hDiv : Nat.div (8 * i + j) 8 = i := by
      rw [Nat.add_comm (8 * i) j, nat_add_mul_div_left _ _ h8pos,
        nat_div_eq_of_lt hj, Nat.zero_add]
    have hMod : Nat.mod (8 * i + j) 8 = j := by
      rw [Nat.add_comm (8 * i) j, nat_add_mul_mod_self_left,
        nat_mod_eq_of_lt hj]
    rw [Anneal.BitVecArith.getLsbD_bswapBytes, decide_eq_true hBound,
      Bool.true_and, hDiv, hMod, Nat.add_comm j (8 * (n - 1 - i))]

/-- `toLeBytes n (toLeWidth (bswapBytes n x)) = toBeBytes n (toLeWidth x)`. -/
theorem toLeBytes_bswapBytes_eq_toBeBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.LeBytes.toLeBytes n (toLeWidth (Anneal.BitVecArith.bswapBytes n x)) =
      Anneal.LeBytes.toBeBytes n (toLeWidth x) :=
  toLeBytes_toLeWidth_bswapBytes n x

/-- `toBeBytes n (toLeWidth (bswapBytes n x)) = toLeBytes n (toLeWidth x)`. -/
theorem toBeBytes_bswapBytes_eq_toLeBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.LeBytes.toBeBytes n (toLeWidth (Anneal.BitVecArith.bswapBytes n x)) =
      Anneal.LeBytes.toLeBytes n (toLeWidth x) := by
  unfold Anneal.LeBytes.toBeBytes
  rw [toLeBytes_toLeWidth_bswapBytes, list_reverse_reverse]

/-- Big-endian decoding of `toLeBytes n (toLeWidth x)` recovers
`(bswapBytes n x).toNat`. -/
theorem fromBeBytes_toLeBytes_eq_bswapBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.LeBytes.fromBeBytes (Anneal.LeBytes.toLeBytes n (toLeWidth x)) =
      (Anneal.BitVecArith.bswapBytes n x).toNat := by
  rw [← toBeBytes_bswapBytes_eq_toLeBytes, Anneal.LeBytes.fromBeBytes_toBeBytes,
    toNat_toLeWidth]

/-- Little-endian decoding of `toBeBytes n (toLeWidth x)` recovers
`(bswapBytes n x).toNat`. -/
theorem fromLeBytes_toBeBytes_eq_bswapBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.LeBytes.fromLeBytes (Anneal.LeBytes.toBeBytes n (toLeWidth x)) =
      (Anneal.BitVecArith.bswapBytes n x).toNat := by
  rw [← toLeBytes_bswapBytes_eq_toBeBytes, Anneal.LeBytes.fromLeBytes_toLeBytes,
    toNat_toLeWidth]

/-- Closed-form equivalence between `bswapBytes n` and
`fromBeBytes ∘ toLeBytes`. -/
theorem bswapBytes_eq_ofNat_fromBeBytes (n : Nat) (x : BitVec (8 * n)) :
    Anneal.BitVecArith.bswapBytes n x =
      BitVec.ofNat (8 * n)
        (Anneal.LeBytes.fromBeBytes
          (Anneal.LeBytes.toLeBytes n (toLeWidth x))) := by
  rw [fromBeBytes_toLeBytes_eq_bswapBytes, ofNat_toNat_self]

/-- Generic `IntWidth` `bvBswap` byte-list law: the little-endian bytes of
`bvBswap w x` are the big-endian bytes of `x` at every width `w`. -/
theorem bvBswap_toLeBytes_eq (w : IntWidth) (x : BitVec (8 * w.byteSize)) :
    Anneal.LeBytes.toLeBytes w.byteSize (toLeWidth (bvBswap w x)) =
      Anneal.LeBytes.toBeBytes w.byteSize (toLeWidth x) :=
  toLeBytes_bswapBytes_eq_toBeBytes w.byteSize x

/-- Cross-endian `encodeVal`: little-endian encoding of `bvBswap w x` produces
identical initialized memory bytes to big-endian encoding of `x`. -/
theorem encodeVal_little_bvBswap_eq_big (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    encodeVal .little (.int w s) (.scalar (bvToScalar w s (bvBswap w x))) =
      encodeVal .big (.int w s) (.scalar (bvToScalar w s x)) := by
  rw [encodeVal_bvToScalar, encodeVal_bvToScalar]
  have hEq :
      encodeUInt .little w.byteSize (bvBswap w x).toNat =
        encodeUInt .big w.byteSize x.toNat := by
    have hL : encodeUInt .little w.byteSize (bvBswap w x).toNat =
        encodeUInt .little w.byteSize (toLeWidth (bvBswap w x)).toNat := rfl
    have hR : encodeUInt .big w.byteSize x.toNat =
        encodeUInt .big w.byteSize (toLeWidth x).toNat := rfl
    rw [hL, hR, encodeUInt_little_eq_toLeBytes, encodeUInt_big_eq_toBeBytes,
      bvBswap_toLeBytes_eq]
  rw [hEq]

/-- Cross-endian `encodeVal`: big-endian encoding of `bvBswap w x` produces
identical initialized memory bytes to little-endian encoding of `x`. -/
theorem encodeVal_big_bvBswap_eq_little (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    encodeVal .big (.int w s) (.scalar (bvToScalar w s (bvBswap w x))) =
      encodeVal .little (.int w s) (.scalar (bvToScalar w s x)) := by
  have h := encodeVal_little_bvBswap_eq_big w s (bvBswap w x)
  rw [bvBswap_bvBswap] at h
  exact h.symm

/-- Endianness round-trip: encoding `x` in big-endian memory and decoding in
little-endian memory yields `bvBswap w x`, and symmetrically for little-to-big.
-/
theorem decodeVal_encodeVal_bvBswap_roundtrip (w : IntWidth) (s : Bool)
    (x : BitVec (8 * w.byteSize)) :
    ∃ bytesBe bytesLe : List AllocByte,
      encodeVal .big (.int w s) (.scalar (bvToScalar w s x)) = .ok bytesBe ∧
      decodeVal .little (.int w s) bytesBe =
        .ok (some (.scalar (bvToScalar w s (bvBswap w x)))) ∧
      encodeVal .little (.int w s) (.scalar (bvToScalar w s x)) = .ok bytesLe ∧
      decodeVal .big (.int w s) bytesLe =
        .ok (some (.scalar (bvToScalar w s (bvBswap w x)))) := by
  let ⟨bytesBe, hEncL, hDecL⟩ :=
    decodeVal_encodeVal_bvToScalar .little w s (bvBswap w x)
  rw [encodeVal_little_bvBswap_eq_big] at hEncL
  let ⟨bytesLe, hEncB, hDecB⟩ :=
    decodeVal_encodeVal_bvToScalar .big w s (bvBswap w x)
  rw [encodeVal_big_bvBswap_eq_little] at hEncB
  exact ⟨bytesBe, bytesLe, hEncL, hDecL, hEncB, hDecB⟩

/-! ## Part 4: Saturating Arithmetic & Exact Division -/

/-- Unsigned saturating addition on `BitVec w`, clamping to `allOnes w` on
overflow. -/
@[expose] def bvSaturatingAddUnsigned {w : Nat} (x y : BitVec w) : BitVec w :=
  if x.toNat + y.toNat < Nat.pow 2 w then x + y else Anneal.BitVec.allOnes w

/-- Unsigned saturating subtraction on `BitVec w`, clamping to `0#w` on
underflow. -/
@[expose] def bvSaturatingSubUnsigned {w : Nat} (x y : BitVec w) : BitVec w :=
  if y ≤ x then x - y else BitVec.ofNat w 0

/-- Exact `.toNat` value of `bvSaturatingAddUnsigned x y`. -/
theorem toNat_bvSaturatingAddUnsigned {w : Nat} (x y : BitVec w) :
    (bvSaturatingAddUnsigned x y).toNat =
      if x.toNat + y.toNat < Nat.pow 2 w then x.toNat + y.toNat
      else Nat.pow 2 w - 1 := by
  unfold bvSaturatingAddUnsigned
  cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 w) with
  | inl hlt =>
    rw [ite_true_of hlt, ite_true_of hlt, Anneal.BitVec.toNat_add,
      nat_mod_eq_of_lt hlt]
  | inr hge =>
    have hnot : ¬ (x.toNat + y.toNat < Nat.pow 2 w) := Nat.not_lt_of_ge hge
    rw [ite_false_of hnot, ite_false_of hnot, Anneal.BitVec.toNat_allOnes]

/-- Clamping bounds for unsigned saturating addition. -/
theorem bvSaturatingAddUnsigned_bounds {w : Nat} (x y : BitVec w) :
    x ≤ bvSaturatingAddUnsigned x y ∧
      y ≤ bvSaturatingAddUnsigned x y ∧
      bvSaturatingAddUnsigned x y ≤ Anneal.BitVec.allOnes w ∧
      (bvSaturatingAddUnsigned x y).toNat ≤ x.toNat + y.toNat := by
  change x.toNat ≤ (bvSaturatingAddUnsigned x y).toNat ∧
    y.toNat ≤ (bvSaturatingAddUnsigned x y).toNat ∧
    (bvSaturatingAddUnsigned x y).toNat ≤ (Anneal.BitVec.allOnes w).toNat ∧
    (bvSaturatingAddUnsigned x y).toNat ≤ x.toNat + y.toNat
  rw [toNat_bvSaturatingAddUnsigned, Anneal.BitVec.toNat_allOnes]
  cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 w) with
  | inl hlt =>
    rw [ite_true_of hlt]
    refine ⟨Nat.le_add_right _ _, Nat.le_add_left _ _,
      Nat.le_sub_one_of_lt hlt, Nat.le_refl _⟩
  | inr hge =>
    have hnot : ¬ (x.toNat + y.toNat < Nat.pow 2 w) := Nat.not_lt_of_ge hge
    rw [ite_false_of hnot]
    refine ⟨Nat.le_sub_one_of_lt x.isLt, Nat.le_sub_one_of_lt y.isLt,
      Nat.le_refl _, Nat.le_trans (Nat.sub_le (Nat.pow 2 w) 1) hge⟩

/-- Commutativity of unsigned saturating addition. -/
theorem bvSaturatingAddUnsigned_comm {w : Nat} (x y : BitVec w) :
    bvSaturatingAddUnsigned x y = bvSaturatingAddUnsigned y x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [toNat_bvSaturatingAddUnsigned, toNat_bvSaturatingAddUnsigned,
    Nat.add_comm x.toNat y.toNat]

/-- Monotonicity of unsigned saturating addition in both operands. -/
theorem bvSaturatingAddUnsigned_mono {w : Nat} {x₁ x₂ y₁ y₂ : BitVec w}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    bvSaturatingAddUnsigned x₁ y₁ ≤ bvSaturatingAddUnsigned x₂ y₂ := by
  change (bvSaturatingAddUnsigned x₁ y₁).toNat ≤
    (bvSaturatingAddUnsigned x₂ y₂).toNat
  rw [toNat_bvSaturatingAddUnsigned, toNat_bvSaturatingAddUnsigned]
  have hsum : x₁.toNat + y₁.toNat ≤ x₂.toNat + y₂.toNat := Nat.add_le_add hx hy
  cases Nat.lt_or_ge (x₁.toNat + y₁.toNat) (Nat.pow 2 w) with
  | inl hlt1 =>
    rw [ite_true_of hlt1]
    cases Nat.lt_or_ge (x₂.toNat + y₂.toNat) (Nat.pow 2 w) with
    | inl hlt2 => rw [ite_true_of hlt2]; exact hsum
    | inr hge2 =>
      rw [ite_false_of (Nat.not_lt_of_ge hge2)]
      exact Nat.le_sub_one_of_lt hlt1
  | inr hge1 =>
    rw [ite_false_of (Nat.not_lt_of_ge hge1),
      ite_false_of (Nat.not_lt_of_ge (Nat.le_trans hge1 hsum))]
    exact Nat.le_refl _

/-- Exact `.toNat` value of `bvSaturatingSubUnsigned x y`: equals `x.toNat -
y.toNat` in both the non-underflowing and clamped cases. -/
theorem toNat_bvSaturatingSubUnsigned {w : Nat} (x y : BitVec w) :
    (bvSaturatingSubUnsigned x y).toNat = x.toNat - y.toNat := by
  unfold bvSaturatingSubUnsigned
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl hlt =>
    have hnot : ¬ (y ≤ x) := Nat.not_le_of_gt hlt
    rw [ite_false_of hnot, Anneal.BitVec.toNat_zero,
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  | inr hge =>
    rw [ite_true_of (c := y ≤ x) hge, Anneal.BitVec.toNat_sub_of_le hge]

/-- Clamping bounds for unsigned saturating subtraction. -/
theorem bvSaturatingSubUnsigned_bounds {w : Nat} (x y : BitVec w) :
    BitVec.ofNat w 0 ≤ bvSaturatingSubUnsigned x y ∧
      bvSaturatingSubUnsigned x y ≤ x := by
  change (BitVec.ofNat w 0).toNat ≤ (bvSaturatingSubUnsigned x y).toNat ∧
    (bvSaturatingSubUnsigned x y).toNat ≤ x.toNat
  rw [Anneal.BitVec.toNat_zero, toNat_bvSaturatingSubUnsigned]
  exact ⟨Nat.zero_le _, Nat.sub_le x.toNat y.toNat⟩

/-- Monotonicity/antitonicity of unsigned saturating subtraction. -/
theorem bvSaturatingSubUnsigned_mono {w : Nat} {x₁ x₂ y₁ y₂ : BitVec w}
    (hx : x₁ ≤ x₂) (hy : y₂ ≤ y₁) :
    bvSaturatingSubUnsigned x₁ y₁ ≤ bvSaturatingSubUnsigned x₂ y₂ := by
  change (bvSaturatingSubUnsigned x₁ y₁).toNat ≤
    (bvSaturatingSubUnsigned x₂ y₂).toNat
  rw [toNat_bvSaturatingSubUnsigned, toNat_bvSaturatingSubUnsigned]
  exact nat_sub_le_sub hx hy

/-- Non-overflow MIR agreement: `evalBinOp .add` on unsigned scalars matches
`bvSaturatingAddUnsigned` whenever `x.toNat + y.toNat < 2^(8 * w.byteSize)`. -/
theorem evalBinOp_add_eq_bvSaturatingAddUnsigned (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)}
    (hNoOvf : x.toNat + y.toNat < Nat.pow 2 (8 * w.byteSize)) :
    evalBinOp .add (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.scalar (bvToScalar w false (bvSaturatingAddUnsigned x y))) := by
  unfold bvSaturatingAddUnsigned
  rw [ite_true_of hNoOvf]
  exact evalBinOp_add_eq_add w false x y

/-- Full unsigned `evalBinOp .addWithOverflow` agreement for
`bvSaturatingAddUnsigned`. -/
theorem evalBinOp_addWithOverflow_saturating_unsigned (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ sum : BitVec (8 * w.byteSize), ∃ ovf : Bool,
      evalBinOp .addWithOverflow (.scalar (bvToScalar w false x))
          (.scalar (bvToScalar w false y)) =
        .ok (.tuple [.scalar (bvToScalar w false sum), .bool ovf]) ∧
      bvSaturatingAddUnsigned x y =
        if ovf then Anneal.BitVec.allOnes (8 * w.byteSize) else sum := by
  refine ⟨x + y, decide (Nat.pow 2 (8 * w.byteSize) ≤ x.toNat + y.toNat),
    evalBinOp_addWithOverflow_unsigned_eq w x y, ?_⟩
  unfold bvSaturatingAddUnsigned
  cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 (8 * w.byteSize)) with
  | inl hlt =>
    rw [ite_true_of hlt, decide_eq_false (Nat.not_le_of_gt hlt)]
    rfl
  | inr hge =>
    rw [ite_false_of (Nat.not_lt_of_ge hge), decide_eq_true hge]
    rfl

/-- Non-underflow MIR agreement: `evalBinOp .sub` on unsigned scalars matches
`bvSaturatingSubUnsigned` whenever `y ≤ x`. -/
theorem evalBinOp_sub_eq_bvSaturatingSubUnsigned (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)} (hle : y ≤ x) :
    evalBinOp .sub (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.scalar (bvToScalar w false (bvSaturatingSubUnsigned x y))) := by
  unfold bvSaturatingSubUnsigned
  rw [ite_true_of (c := y ≤ x) hle]
  exact evalBinOp_sub_eq_sub w false x y

/-- Full unsigned `evalBinOp .subWithOverflow` agreement for
`bvSaturatingSubUnsigned`. -/
theorem evalBinOp_subWithOverflow_saturating_unsigned (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ diff : BitVec (8 * w.byteSize), ∃ ovf : Bool,
      evalBinOp .subWithOverflow (.scalar (bvToScalar w false x))
          (.scalar (bvToScalar w false y)) =
        .ok (.tuple [.scalar (bvToScalar w false diff), .bool ovf]) ∧
      bvSaturatingSubUnsigned x y =
        if ovf then BitVec.ofNat (8 * w.byteSize) 0 else diff := by
  refine ⟨x - y, decide (x.toNat < y.toNat),
    evalBinOp_subWithOverflow_unsigned_eq w x y, ?_⟩
  unfold bvSaturatingSubUnsigned
  cases Nat.lt_or_ge x.toNat y.toNat with
  | inl hlt =>
    rw [ite_false_of (c := y ≤ x) (Nat.not_le_of_gt hlt), decide_eq_true hlt]
    rfl
  | inr hge =>
    rw [ite_true_of (c := y ≤ x) hge, decide_eq_false (Nat.not_lt_of_ge hge)]
    rfl

/-- Maximum two's-complement signed bitvector `2^(w - 1) - 1` (`INT_MAX`). -/
@[expose] def signedMaxBv (w : Nat) : BitVec w :=
  Anneal.BitVec.not (Anneal.BitVecArith.signBit (w := w))

private theorem signedKey_signBit {w : Nat} (hw : 0 < w) :
    Anneal.BitVecArith.signedKey (Anneal.BitVecArith.signBit (w := w)) = 0 := by
  have hm : Anneal.BitVecArith.msb (Anneal.BitVecArith.signBit (w := w)) =
      true := by
    rw [Anneal.BitVecArith.msb_eq_true_iff hw,
      Anneal.BitVecArith.toNat_signBit_of_pos hw]
    exact Nat.le_refl _
  rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hw hm,
    Anneal.BitVecArith.toNat_signBit_of_pos hw, Nat.sub_self]

private theorem signedMaxBv_toNat {w : Nat} (hw : 0 < w) :
    (signedMaxBv w).toNat = Nat.pow 2 (w - 1) - 1 := by
  unfold signedMaxBv
  rw [Anneal.BitVecArith.toNat_not_eq_sub,
    Anneal.BitVecArith.toNat_signBit_of_pos hw, nat_two_pow_split hw,
    Nat.add_comm (Nat.pow 2 (w - 1)) (Nat.pow 2 (w - 1)),
    nat_sub_right_comm, Nat.add_sub_cancel]

private theorem msb_signedMaxBv {w : Nat} (hw : 0 < w) :
    Anneal.BitVecArith.msb (signedMaxBv w) = false := by
  rw [Anneal.BitVecArith.msb_eq_false_iff hw, signedMaxBv_toNat hw]
  exact Nat.sub_lt (nat_two_pow_pos (w - 1)) Nat.one_pos

private theorem signedKey_signedMaxBv {w : Nat} (hw : 0 < w) :
    Anneal.BitVecArith.signedKey (signedMaxBv w) = Nat.pow 2 w - 1 := by
  rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hw (msb_signedMaxBv hw),
    signedMaxBv_toNat hw, nat_two_pow_split hw,
    nat_sub_add_comm (nat_two_pow_pos (w - 1))]

/-- Exact `bvToInt` value of `signedMaxBv w` for `0 < w`. -/
theorem bvToInt_signedMaxBv {w : Nat} (hw : 0 < w) :
    bvToInt (signedMaxBv w) = Int.ofNat (Nat.pow 2 (w - 1) - 1) := by
  have hm := msb_signedMaxBv hw
  have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hw (signedMaxBv w)).1 hm
  have h2 : 2 * (signedMaxBv w).toNat < Nat.pow 2 w := by
    rw [nat_two_pow_split hw, Nat.two_mul]
    exact Nat.add_lt_add hxLt hxLt
  unfold bvToInt
  rw [ite_true_of h2, signedMaxBv_toNat hw]

/-- Exact equivalence between `bvToInt x ≤ bvToInt y` and
`Anneal.BitVecArith.sle x y` for any positive width `w`. -/
theorem bvToInt_le_iff_sle {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    bvToInt x ≤ bvToInt y ↔ Anneal.BitVecArith.sle x y := by
  rw [intBalance_le_iff (intBalance_bvToInt hw x) (intBalance_bvToInt hw y)]
  exact ⟨Nat.le_of_add_le_add_right,
    fun h => Nat.add_le_add_right h (Nat.pow 2 (w - 1))⟩

/-- `signBit` (`INT_MIN`) is the least `w`-bit vector under signed order `sle`.
-/
theorem sle_signBit {w : Nat} (hw : 0 < w) (x : BitVec w) :
    Anneal.BitVecArith.sle (Anneal.BitVecArith.signBit (w := w)) x := by
  unfold Anneal.BitVecArith.sle
  rw [signedKey_signBit hw]
  exact Nat.zero_le _

/-- `signedMaxBv w` (`INT_MAX`) is the greatest `w`-bit vector under signed
order `sle`. -/
theorem sle_signedMaxBv {w : Nat} (hw : 0 < w) (x : BitVec w) :
    Anneal.BitVecArith.sle x (signedMaxBv w) := by
  unfold Anneal.BitVecArith.sle
  rw [signedKey_signedMaxBv hw]
  exact Nat.le_sub_one_of_lt (Anneal.BitVecArith.signedKey_lt x)

/-- Signed saturating addition on `BitVec w`, clamping to `signBit` (`INT_MIN`)
or `signedMaxBv w` (`INT_MAX`) on signed overflow. -/
@[expose] def bvSaturatingAddSigned {w : Nat} (x y : BitVec w) : BitVec w :=
  if signedOverflowAddBv x y then
    if Anneal.BitVecArith.msb x then Anneal.BitVecArith.signBit (w := w)
    else signedMaxBv w
  else
    x + y

/-- Signed saturating subtraction on `BitVec w`, clamping to `signBit`
(`INT_MIN`) or `signedMaxBv w` (`INT_MAX`) on signed overflow. -/
@[expose] def bvSaturatingSubSigned {w : Nat} (x y : BitVec w) : BitVec w :=
  if signedOverflowSubBv x y then
    if Anneal.BitVecArith.msb x then Anneal.BitVecArith.signBit (w := w)
    else signedMaxBv w
  else
    x - y

private theorem signedKey_add_of_no_overflow {w : Nat} (hw : 0 < w)
    {x y : BitVec w} (hNoOvf : signedOverflowAddBv x y = false) :
    Anneal.BitVecArith.signedKey (x + y) =
      Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y -
        Nat.pow 2 (w - 1) := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  unfold signedOverflowAddBv at hNoOvf
  cases hmx : Anneal.BitVecArith.msb x <;>
    cases hmy : Anneal.BitVecArith.msb y
  · have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hw x).1 hmx
    have hyLt := (Anneal.BitVecArith.msb_eq_false_iff hw y).1 hmy
    have hsumLt : x.toNat + y.toNat < Nat.pow 2 w := by
      rw [hPow]
      exact Nat.add_lt_add hxLt hyLt
    have hzNat : (x + y).toNat = x.toNat + y.toNat := by
      rw [Anneal.BitVec.toNat_add, nat_mod_eq_of_lt hsumLt]
    rw [hmx, hmy] at hNoOvf
    have hmz : Anneal.BitVecArith.msb (x + y) = false := by
      cases hc : Anneal.BitVecArith.msb (x + y) with
      | false => rfl
      | true => rw [hc] at hNoOvf; nomatch hNoOvf
    rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmz, hzNat,
      Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmx,
      Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmy]
    have hEq2 : (x.toNat + H) + (y.toNat + H) =
        (x.toNat + y.toNat + H) + H := by
      rw [add_four_rearrange x.toNat H y.toNat H, ← Nat.add_assoc]
    rw [hEq2, Nat.add_sub_cancel]
  · have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hw x).1 hmx
    have hyGe := (Anneal.BitVecArith.msb_eq_true_iff hw y).1 hmy
    rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmx,
      Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmy]
    cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 w) with
    | inl hlt =>
      have hzNat : (x + y).toNat = x.toNat + y.toNat := by
        rw [Anneal.BitVec.toNat_add, nat_mod_eq_of_lt hlt]
      have hzGe : H ≤ (x + y).toNat := by
        rw [hzNat]
        exact Nat.le_trans hyGe (Nat.le_add_left _ _)
      have hmz : Anneal.BitVecArith.msb (x + y) = true :=
        (Anneal.BitVecArith.msb_eq_true_iff hw _).2 hzGe
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmz, hzNat]
      have h1 : (x.toNat + H) + (y.toNat - H) = x.toNat + y.toNat := by
        rw [Nat.add_assoc, Nat.add_comm H (y.toNat - H),
          Nat.sub_add_cancel hyGe]
      rw [h1]
    | inr hge =>
      have hsumLt : x.toNat + y.toNat < H + Nat.pow 2 w :=
        Nat.add_lt_add hxLt (bitVec_toNat_lt_pow y)
      have hzNat : (x + y).toNat = x.toNat + y.toNat - Nat.pow 2 w := by
        have hSp : x.toNat + y.toNat =
            (x.toNat + y.toNat - Nat.pow 2 w) + Nat.pow 2 w :=
          (Nat.sub_add_cancel hge).symm
        have hSubLt : x.toNat + y.toNat - Nat.pow 2 w < Nat.pow 2 w :=
          nat_sub_lt_of_lt_add (nat_two_pow_pos w)
            (Nat.add_lt_add (bitVec_toNat_lt_pow x) (bitVec_toNat_lt_pow y))
        have hModEq :
            Nat.mod (x.toNat + y.toNat) (Nat.pow 2 w) =
              x.toNat + y.toNat - Nat.pow 2 w := by
          rw [hSp, nat_add_mod_left, nat_mod_eq_of_lt hSubLt, Nat.add_sub_cancel]
        rw [Anneal.BitVec.toNat_add, hModEq]
      have hzLt : (x + y).toNat < H := by
        rw [hzNat]
        exact nat_sub_lt_of_lt_add (nat_two_pow_pos (w - 1)) hsumLt
      have hmz : Anneal.BitVecArith.msb (x + y) = false :=
        (Anneal.BitVecArith.msb_eq_false_iff hw _).2 hzLt
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmz, hzNat]
      have h1 : (x.toNat + H) + (y.toNat - H) = x.toNat + y.toNat := by
        rw [Nat.add_assoc, Nat.add_comm H (y.toNat - H),
          Nat.sub_add_cancel hyGe]
      rw [h1]
      apply Nat.add_right_cancel (m := Nat.pow 2 w)
      have hSubLe : H ≤ x.toNat + y.toNat := Nat.le_trans (by
        rw [hPow]; exact Nat.le_add_right H H) hge
      rw [Nat.add_assoc (x.toNat + y.toNat - Nat.pow 2 w) H (Nat.pow 2 w),
        Nat.add_comm H (Nat.pow 2 w), ← Nat.add_assoc,
        Nat.sub_add_cancel hge, hPow, ← Nat.add_assoc,
        Nat.sub_add_cancel hSubLe]
  · have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).1 hmx
    have hyLt := (Anneal.BitVecArith.msb_eq_false_iff hw y).1 hmy
    rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmx,
      Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmy]
    cases Nat.lt_or_ge (x.toNat + y.toNat) (Nat.pow 2 w) with
    | inl hlt =>
      have hzNat : (x + y).toNat = x.toNat + y.toNat := by
        rw [Anneal.BitVec.toNat_add, nat_mod_eq_of_lt hlt]
      have hzGe : H ≤ (x + y).toNat := by
        rw [hzNat]
        exact Nat.le_trans hxGe (Nat.le_add_right _ _)
      have hmz : Anneal.BitVecArith.msb (x + y) = true :=
        (Anneal.BitVecArith.msb_eq_true_iff hw _).2 hzGe
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmz, hzNat]
      have h1 : (x.toNat - H) + (y.toNat + H) = x.toNat + y.toNat := by
        rw [Nat.add_comm y.toNat H, ← Nat.add_assoc,
          Nat.sub_add_cancel hxGe]
      rw [h1]
    | inr hge =>
      have hsumLt : x.toNat + y.toNat < H + Nat.pow 2 w := by
        rw [Nat.add_comm H (Nat.pow 2 w)]
        exact Nat.add_lt_add (bitVec_toNat_lt_pow x) hyLt
      have hzNat : (x + y).toNat = x.toNat + y.toNat - Nat.pow 2 w := by
        have hSp : x.toNat + y.toNat =
            (x.toNat + y.toNat - Nat.pow 2 w) + Nat.pow 2 w :=
          (Nat.sub_add_cancel hge).symm
        have hSubLt : x.toNat + y.toNat - Nat.pow 2 w < Nat.pow 2 w :=
          nat_sub_lt_of_lt_add (nat_two_pow_pos w)
            (Nat.add_lt_add (bitVec_toNat_lt_pow x) (bitVec_toNat_lt_pow y))
        have hModEq :
            Nat.mod (x.toNat + y.toNat) (Nat.pow 2 w) =
              x.toNat + y.toNat - Nat.pow 2 w := by
          rw [hSp, nat_add_mod_left, nat_mod_eq_of_lt hSubLt, Nat.add_sub_cancel]
        rw [Anneal.BitVec.toNat_add, hModEq]
      have hzLt : (x + y).toNat < H := by
        rw [hzNat]
        exact nat_sub_lt_of_lt_add (nat_two_pow_pos (w - 1)) hsumLt
      have hmz : Anneal.BitVecArith.msb (x + y) = false :=
        (Anneal.BitVecArith.msb_eq_false_iff hw _).2 hzLt
      rw [Anneal.BitVecArith.signedKey_eq_of_msb_false hw hmz, hzNat]
      have h1 : (x.toNat - H) + (y.toNat + H) = x.toNat + y.toNat := by
        rw [Nat.add_comm y.toNat H, ← Nat.add_assoc,
          Nat.sub_add_cancel hxGe]
      rw [h1]
      apply Nat.add_right_cancel (m := Nat.pow 2 w)
      have hSubLe : H ≤ x.toNat + y.toNat := Nat.le_trans (by
        rw [hPow]; exact Nat.le_add_right H H) hge
      rw [Nat.add_assoc (x.toNat + y.toNat - Nat.pow 2 w) H (Nat.pow 2 w),
        Nat.add_comm H (Nat.pow 2 w), ← Nat.add_assoc,
        Nat.sub_add_cancel hge, hPow, ← Nat.add_assoc,
        Nat.sub_add_cancel hSubLe]
  · have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).1 hmx
    have hyGe := (Anneal.BitVecArith.msb_eq_true_iff hw y).1 hmy
    rw [hmx, hmy] at hNoOvf
    have hmz : Anneal.BitVecArith.msb (x + y) = true := by
      cases hc : Anneal.BitVecArith.msb (x + y) with
      | true => rfl
      | false => rw [hc] at hNoOvf; nomatch hNoOvf
    have hge : Nat.pow 2 w ≤ x.toNat + y.toNat := by
      rw [hPow]; exact Nat.add_le_add hxGe hyGe
    have hsumLt : x.toNat + y.toNat < Nat.pow 2 w + Nat.pow 2 w :=
      Nat.add_lt_add x.isLt y.isLt
    have hzNat : (x + y).toNat = x.toNat + y.toNat - Nat.pow 2 w := by
      have hSp : x.toNat + y.toNat =
          (x.toNat + y.toNat - Nat.pow 2 w) + Nat.pow 2 w :=
        (Nat.sub_add_cancel hge).symm
      have hSubLt : x.toNat + y.toNat - Nat.pow 2 w < Nat.pow 2 w :=
        nat_sub_lt_of_lt_add (nat_two_pow_pos w) hsumLt
      have hModEq :
          Nat.mod (x.toNat + y.toNat) (Nat.pow 2 w) =
            x.toNat + y.toNat - Nat.pow 2 w := by
        rw [hSp, nat_add_mod_left, nat_mod_eq_of_lt hSubLt, Nat.add_sub_cancel]
      rw [Anneal.BitVec.toNat_add, hModEq]
    have hzGe := (Anneal.BitVecArith.msb_eq_true_iff hw _).1 hmz
    rw [Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmz, hzNat,
      Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmx,
      Anneal.BitVecArith.signedKey_eq_of_msb_true hw hmy]
    apply Nat.add_right_cancel (m := Nat.pow 2 w + H)
    have h1 : ((x.toNat - H) + (y.toNat - H)) + (H + H) = x.toNat + y.toNat := by
      rw [add_four_rearrange (x.toNat - H) (y.toNat - H) H H,
        Nat.sub_add_cancel hxGe, Nat.sub_add_cancel hyGe]
    have hH2 : (x.toNat + y.toNat - Nat.pow 2 w - H) + (Nat.pow 2 w + H) =
        x.toNat + y.toNat := by
      rw [Nat.add_comm (Nat.pow 2 w) H, ← Nat.add_assoc, ← hzNat,
        Nat.sub_add_cancel hzGe, hzNat, Nat.sub_add_cancel hge]
    have hSubH : H ≤ (x.toNat - H) + (y.toNat - H) := by
      have h3 : (x.toNat + y.toNat - (H + H)) + (H + H) = x.toNat + y.toNat :=
        Nat.sub_add_cancel (by rw [← hPow]; exact hge)
      have hLe1 : H + (H + H) ≤ (x.toNat + y.toNat - (H + H)) + (H + H) :=
        Nat.add_le_add_right (by rw [← hPow, ← hzNat]; exact hzGe) (H + H)
      rw [h3, ← h1, ← hPow] at hLe1
      exact Nat.le_of_add_le_add_right hLe1
    rw [hH2, Nat.add_comm (Nat.pow 2 w) H, ← Nat.add_assoc,
      Nat.sub_add_cancel hSubH, hPow, h1]

private theorem signedKey_sub_of_no_overflow {w : Nat} (hw : 0 < w)
    {x y : BitVec w} (hNoOvf : signedOverflowSubBv x y = false) :
    Anneal.BitVecArith.signedKey (x - y) =
      Anneal.BitVecArith.signedKey x + Nat.pow 2 (w - 1) -
        Anneal.BitVecArith.signedKey y := by
  have h := (signedOverflowSubBv_eq_false_iff hw x y).1 hNoOvf
  exact signedKey_sub_no_overflow hw h.1 h.2

/-- Exact `signedKey` equation for signed saturating addition (`clamp` of
`signedKey x + signedKey y - 2^(w - 1)` to `[0, 2^w - 1]`). -/
theorem signedKey_bvSaturatingAddSigned {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    Anneal.BitVecArith.signedKey (bvSaturatingAddSigned x y) =
      if Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y <
          Nat.pow 2 (w - 1) then
        0
      else if Nat.pow 2 (w - 1) + Nat.pow 2 w ≤
          Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y then
        Nat.pow 2 w - 1
      else
        Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y -
          Nat.pow 2 (w - 1) := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  unfold bvSaturatingAddSigned
  cases hOv : signedOverflowAddBv x y with
  | false =>
    have hB := (signedOverflowAddBv_eq_false_iff hw x y).1 hOv
    rw [bv_ite_bool_false_eq rfl, ite_false_of (Nat.not_lt_of_ge hB.1),
      ite_false_of (Nat.not_le_of_gt hB.2)]
    exact signedKey_add_of_no_overflow hw hOv
  | true =>
    rw [bv_ite_bool_true_eq rfl]
    have hSame : Anneal.BitVecArith.msb x = Anneal.BitVecArith.msb y := by
      unfold signedOverflowAddBv at hOv
      exact of_decide_eq_true (bool_and_left hOv)
    cases hmx : Anneal.BitVecArith.msb x with
    | true =>
      have hmy : Anneal.BitVecArith.msb y = true := hSame.symm.trans hmx
      have hkx := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
      have hky := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
      have hSumLtOvf : Anneal.BitVecArith.signedKey x +
          Anneal.BitVecArith.signedKey y < H := by
        cases Nat.lt_or_ge
            (Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y)
            H with
        | inl hlt => exact hlt
        | inr hge =>
          have hHi : Anneal.BitVecArith.signedKey x +
              Anneal.BitVecArith.signedKey y < H + Nat.pow 2 w := by
            rw [hPow, ← Nat.add_assoc]
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add hkx hky)
              (Nat.le_add_right _ _)
          have hF := (signedOverflowAddBv_eq_false_iff hw x y).2 ⟨hge, hHi⟩
          rw [hF] at hOv
          nomatch hOv
      rw [bv_ite_bool_true_eq rfl, signedKey_signBit hw, ite_true_of hSumLtOvf]
    | false =>
      have hmy : Anneal.BitVecArith.msb y = false := hSame.symm.trans hmx
      have hkx := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
      have hky := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
      have hSumGeH : H ≤ Anneal.BitVecArith.signedKey x +
          Anneal.BitVecArith.signedKey y :=
        Nat.le_trans hkx (Nat.le_add_right _ _)
      have hSumGeHi : H + Nat.pow 2 w ≤ Anneal.BitVecArith.signedKey x +
          Anneal.BitVecArith.signedKey y := by
        cases Nat.lt_or_ge
            (Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y)
            (H + Nat.pow 2 w) with
        | inl hlt =>
          have hF := (signedOverflowAddBv_eq_false_iff hw x y).2 ⟨hSumGeH, hlt⟩
          rw [hF] at hOv
          nomatch hOv
        | inr hge => exact hge
      rw [bv_ite_bool_false_eq rfl, signedKey_signedMaxBv hw,
        ite_false_of (Nat.not_lt_of_ge hSumGeH), ite_true_of hSumGeHi]

/-- Exact `signedKey` equation for signed saturating subtraction (`clamp` of
`signedKey x + 2^(w - 1) - signedKey y` to `[0, 2^w - 1]`). -/
theorem signedKey_bvSaturatingSubSigned {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    Anneal.BitVecArith.signedKey (bvSaturatingSubSigned x y) =
      if Anneal.BitVecArith.signedKey x + Nat.pow 2 (w - 1) <
          Anneal.BitVecArith.signedKey y then
        0
      else if Nat.pow 2 w ≤
          Anneal.BitVecArith.signedKey x + Nat.pow 2 (w - 1) -
            Anneal.BitVecArith.signedKey y then
        Nat.pow 2 w - 1
      else
        Anneal.BitVecArith.signedKey x + Nat.pow 2 (w - 1) -
          Anneal.BitVecArith.signedKey y := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  unfold bvSaturatingSubSigned
  cases hOv : signedOverflowSubBv x y with
  | false =>
    have hB := (signedOverflowSubBv_eq_false_iff hw x y).1 hOv
    have hSubLt : Anneal.BitVecArith.signedKey x + H -
        Anneal.BitVecArith.signedKey y < Nat.pow 2 w := by
      apply nat_sub_lt_of_lt_add (nat_two_pow_pos w)
      rw [hPow, Nat.add_assoc H H _, Nat.add_comm H (Anneal.BitVecArith.signedKey y),
        ← Nat.add_assoc H (Anneal.BitVecArith.signedKey y) H,
        Nat.add_comm H (Anneal.BitVecArith.signedKey y)]
      exact Nat.add_lt_add_right hB.2 H
    rw [bv_ite_bool_false_eq rfl, ite_false_of (Nat.not_lt_of_ge hB.1),
      ite_false_of (Nat.not_le_of_gt hSubLt)]
    exact signedKey_sub_of_no_overflow hw hOv
  | true =>
    rw [bv_ite_bool_true_eq rfl]
    have hDiff : Anneal.BitVecArith.msb x ≠ Anneal.BitVecArith.msb y := by
      unfold signedOverflowSubBv at hOv
      exact bne_iff_ne.mp (bool_and_left hOv)
    cases hmx : Anneal.BitVecArith.msb x with
    | true =>
      have hmy : Anneal.BitVecArith.msb y = false := by
        cases hc : Anneal.BitVecArith.msb y with
        | false => rfl
        | true => exact False.elim (hDiff (hmx.trans hc.symm))
      have hkx := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
      have hky := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
      have hUdf : Anneal.BitVecArith.signedKey x + H <
          Anneal.BitVecArith.signedKey y := by
        cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x + H)
            (Anneal.BitVecArith.signedKey y) with
        | inl hlt => exact hlt
        | inr hge =>
          have hHi : Anneal.BitVecArith.signedKey x <
              Anneal.BitVecArith.signedKey y + H :=
            Nat.lt_of_lt_of_le hkx (Nat.le_trans (Nat.le_add_right H H)
              (Nat.add_le_add_right hky H))
          have hF := (signedOverflowSubBv_eq_false_iff hw x y).2 ⟨hge, hHi⟩
          rw [hF] at hOv
          nomatch hOv
      rw [bv_ite_bool_true_eq rfl, signedKey_signBit hw, ite_true_of hUdf]
    | false =>
      have hmy : Anneal.BitVecArith.msb y = true := by
        cases hc : Anneal.BitVecArith.msb y with
        | true => rfl
        | false => exact False.elim (hDiff (hmx.trans hc.symm))
      have hkx := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
      have hky := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
      have hNoUdf : Anneal.BitVecArith.signedKey y ≤
          Anneal.BitVecArith.signedKey x + H :=
        Nat.le_trans (Nat.le_of_lt hky) (Nat.le_trans hkx (Nat.le_add_right _ _))
      have hOvf : Anneal.BitVecArith.signedKey y + H ≤
          Anneal.BitVecArith.signedKey x := by
        cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x)
            (Anneal.BitVecArith.signedKey y + H) with
        | inr hge => exact hge
        | inl hlt =>
          have hF := (signedOverflowSubBv_eq_false_iff hw x y).2 ⟨hNoUdf, hlt⟩
          rw [hF] at hOv
          nomatch hOv
      have hSubGe : Nat.pow 2 w ≤
          Anneal.BitVecArith.signedKey x + H - Anneal.BitVecArith.signedKey y := by
        apply Nat.le_sub_of_add_le
        rw [hPow, Nat.add_comm (H + H) _, ← Nat.add_assoc]
        exact Nat.add_le_add_right hOvf H
      rw [bv_ite_bool_false_eq rfl, signedKey_signedMaxBv hw,
        ite_false_of (Nat.not_lt_of_ge hNoUdf), ite_true_of hSubGe]

/-- Universal clamping bounds for signed saturating addition (`INT_MIN ≤
bvSaturatingAddSigned x y ≤ INT_MAX`). -/
theorem bvSaturatingAddSigned_bounds {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    Anneal.BitVecArith.sle (Anneal.BitVecArith.signBit (w := w))
        (bvSaturatingAddSigned x y) ∧
      Anneal.BitVecArith.sle (bvSaturatingAddSigned x y) (signedMaxBv w) ∧
      Neg.neg (Int.ofNat (Nat.pow 2 (w - 1))) ≤
        bvToInt (bvSaturatingAddSigned x y) ∧
      bvToInt (bvSaturatingAddSigned x y) ≤
        Int.ofNat (Nat.pow 2 (w - 1) - 1) := by
  have hB := bvToInt_in_width_range hw (bvSaturatingAddSigned x y)
  have hLeMax : bvToInt (bvSaturatingAddSigned x y) ≤
      bvToInt (signedMaxBv w) :=
    (bvToInt_le_iff_sle hw _ _).mpr (sle_signedMaxBv hw _)
  rw [bvToInt_signedMaxBv hw] at hLeMax
  exact ⟨sle_signBit hw _, sle_signedMaxBv hw _, hB.1, hLeMax⟩

/-- Universal clamping bounds for signed saturating subtraction (`INT_MIN ≤
bvSaturatingSubSigned x y ≤ INT_MAX`). -/
theorem bvSaturatingSubSigned_bounds {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    Anneal.BitVecArith.sle (Anneal.BitVecArith.signBit (w := w))
        (bvSaturatingSubSigned x y) ∧
      Anneal.BitVecArith.sle (bvSaturatingSubSigned x y) (signedMaxBv w) ∧
      Neg.neg (Int.ofNat (Nat.pow 2 (w - 1))) ≤
        bvToInt (bvSaturatingSubSigned x y) ∧
      bvToInt (bvSaturatingSubSigned x y) ≤
        Int.ofNat (Nat.pow 2 (w - 1) - 1) := by
  have hB := bvToInt_in_width_range hw (bvSaturatingSubSigned x y)
  have hLeMax : bvToInt (bvSaturatingSubSigned x y) ≤
      bvToInt (signedMaxBv w) :=
    (bvToInt_le_iff_sle hw _ _).mpr (sle_signedMaxBv hw _)
  rw [bvToInt_signedMaxBv hw] at hLeMax
  exact ⟨sle_signBit hw _, sle_signedMaxBv hw _, hB.1, hLeMax⟩

/-- Monotonicity of signed saturating addition under `Anneal.BitVecArith.sle`.
-/
theorem bvSaturatingAddSigned_mono {w : Nat} (hw : 0 < w)
    {x₁ x₂ y₁ y₂ : BitVec w}
    (hx : Anneal.BitVecArith.sle x₁ x₂)
    (hy : Anneal.BitVecArith.sle y₁ y₂) :
    Anneal.BitVecArith.sle (bvSaturatingAddSigned x₁ y₁)
      (bvSaturatingAddSigned x₂ y₂) := by
  unfold Anneal.BitVecArith.sle at hx hy
  unfold Anneal.BitVecArith.sle
  rw [signedKey_bvSaturatingAddSigned hw, signedKey_bvSaturatingAddSigned hw]
  let H := Nat.pow 2 (w - 1)
  have hsum : Anneal.BitVecArith.signedKey x₁ + Anneal.BitVecArith.signedKey y₁ ≤
      Anneal.BitVecArith.signedKey x₂ + Anneal.BitVecArith.signedKey y₂ :=
    Nat.add_le_add hx hy
  have hMax : Nat.pow 2 w - 1 < H + Nat.pow 2 w - H := by
    rw [Nat.add_comm H (Nat.pow 2 w), Nat.add_sub_cancel]
    exact Nat.sub_lt (nat_two_pow_pos w) Nat.one_pos
  cases Nat.lt_or_ge
      (Anneal.BitVecArith.signedKey x₁ + Anneal.BitVecArith.signedKey y₁) H with
  | inl h1 =>
    rw [ite_true_of h1]
    exact Nat.zero_le _
  | inr h1 =>
    have h2 : H ≤ Anneal.BitVecArith.signedKey x₂ +
        Anneal.BitVecArith.signedKey y₂ := Nat.le_trans h1 hsum
    rw [ite_false_of (Nat.not_lt_of_ge h1), ite_false_of (Nat.not_lt_of_ge h2)]
    cases Nat.lt_or_ge
        (Anneal.BitVecArith.signedKey x₂ + Anneal.BitVecArith.signedKey y₂)
        (H + Nat.pow 2 w) with
    | inr hhi2 =>
      rw [ite_true_of hhi2]
      cases Nat.lt_or_ge
          (Anneal.BitVecArith.signedKey x₁ + Anneal.BitVecArith.signedKey y₁)
          (H + Nat.pow 2 w) with
      | inl hhi1 =>
        rw [ite_false_of (Nat.not_le_of_gt hhi1)]
        apply Nat.le_sub_one_of_lt
        exact nat_sub_lt_of_lt_add (nat_two_pow_pos w)
          (by rw [Nat.add_comm (Nat.pow 2 w) H]; exact hhi1)
      | inr hhi1 =>
        rw [ite_true_of hhi1]
        exact Nat.le_refl _
    | inl hhi2 =>
      have hhi1 : Anneal.BitVecArith.signedKey x₁ +
          Anneal.BitVecArith.signedKey y₁ < H + Nat.pow 2 w :=
        Nat.lt_of_le_of_lt hsum hhi2
      rw [ite_false_of (Nat.not_le_of_gt hhi1),
        ite_false_of (Nat.not_le_of_gt hhi2)]
      exact Nat.sub_le_sub_right hsum H

/-- Monotonicity/antitonicity of signed saturating subtraction under
`Anneal.BitVecArith.sle`. -/
theorem bvSaturatingSubSigned_mono {w : Nat} (hw : 0 < w)
    {x₁ x₂ y₁ y₂ : BitVec w}
    (hx : Anneal.BitVecArith.sle x₁ x₂)
    (hy : Anneal.BitVecArith.sle y₂ y₁) :
    Anneal.BitVecArith.sle (bvSaturatingSubSigned x₁ y₁)
      (bvSaturatingSubSigned x₂ y₂) := by
  unfold Anneal.BitVecArith.sle at hx hy
  unfold Anneal.BitVecArith.sle
  rw [signedKey_bvSaturatingSubSigned hw, signedKey_bvSaturatingSubSigned hw]
  let H := Nat.pow 2 (w - 1)
  cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x₁ + H)
      (Anneal.BitVecArith.signedKey y₁) with
  | inl h1 =>
    rw [ite_true_of h1]
    exact Nat.zero_le _
  | inr h1 =>
    have h2 : Anneal.BitVecArith.signedKey y₂ ≤
        Anneal.BitVecArith.signedKey x₂ + H :=
      Nat.le_trans hy (Nat.le_trans h1 (Nat.add_le_add_right hx H))
    rw [ite_false_of (Nat.not_lt_of_ge h1), ite_false_of (Nat.not_lt_of_ge h2)]
    have hSub : Anneal.BitVecArith.signedKey x₁ + H -
          Anneal.BitVecArith.signedKey y₁ ≤
        Anneal.BitVecArith.signedKey x₂ + H -
          Anneal.BitVecArith.signedKey y₂ :=
      nat_sub_le_sub (Nat.add_le_add_right hx H) hy
    cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x₂ + H -
        Anneal.BitVecArith.signedKey y₂) (Nat.pow 2 w) with
    | inr hhi2 =>
      rw [ite_true_of hhi2]
      cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x₁ + H -
          Anneal.BitVecArith.signedKey y₁) (Nat.pow 2 w) with
      | inl hhi1 =>
        rw [ite_false_of (Nat.not_le_of_gt hhi1)]
        exact Nat.le_sub_one_of_lt hhi1
      | inr hhi1 =>
        rw [ite_true_of hhi1]
        exact Nat.le_refl _
    | inl hhi2 =>
      have hhi1 : Anneal.BitVecArith.signedKey x₁ + H -
          Anneal.BitVecArith.signedKey y₁ < Nat.pow 2 w :=
        Nat.lt_of_le_of_lt hSub hhi2
      rw [ite_false_of (Nat.not_le_of_gt hhi1),
        ite_false_of (Nat.not_le_of_gt hhi2)]
      exact hSub

/-- Commutativity of signed saturating addition for any positive bit width. -/
theorem bvSaturatingAddSigned_comm {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    bvSaturatingAddSigned x y = bvSaturatingAddSigned y x := by
  apply Anneal.BitVecArith.signedKey_injective
  rw [signedKey_bvSaturatingAddSigned hw, signedKey_bvSaturatingAddSigned hw,
    Nat.add_comm (Anneal.BitVecArith.signedKey x) (Anneal.BitVecArith.signedKey y)]

private theorem int_eq_of_intBalance_eq {a b : Int} {pa na pb nb : Nat}
    (ha : IntBalance a pa na) (hb : IntBalance b pb nb)
    (h : pa + nb = pb + na) : a = b :=
  int_le_antisymm
    ((intBalance_le_iff ha hb).2 (Nat.le_of_eq h))
    ((intBalance_le_iff hb ha).2 (Nat.le_of_eq h.symm))

/-- Non-overflow signed addition `bvToInt` identity. -/
theorem bvToInt_add_of_no_overflow {w : Nat} (hw : 0 < w) {x y : BitVec w}
    (hNoOvf : signedOverflowAddBv x y = false) :
    bvToInt (x + y) = bvToInt x + bvToInt y := by
  let H := Nat.pow 2 (w - 1)
  have hBnd := (signedOverflowAddBv_eq_false_iff hw x y).1 hNoOvf
  have hK : Anneal.BitVecArith.signedKey (x + y) + H =
      Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y := by
    rw [signedKey_add_of_no_overflow hw hNoOvf, Nat.sub_add_cancel hBnd.1]
  apply int_eq_of_intBalance_eq (intBalance_bvToInt hw (x + y))
    (intBalance_add_of (intBalance_bvToInt hw x) (intBalance_bvToInt hw y))
  rw [← Nat.add_assoc, hK]

/-- Non-overflow signed subtraction `bvToInt` identity. -/
theorem bvToInt_sub_of_no_overflow {w : Nat} (hw : 0 < w) {x y : BitVec w}
    (hNoOvf : signedOverflowSubBv x y = false) :
    bvToInt (x - y) = bvToInt x - bvToInt y := by
  let H := Nat.pow 2 (w - 1)
  have hBnd := (signedOverflowSubBv_eq_false_iff hw x y).1 hNoOvf
  have hK : Anneal.BitVecArith.signedKey (x - y) +
      Anneal.BitVecArith.signedKey y = Anneal.BitVecArith.signedKey x + H := by
    rw [signedKey_sub_of_no_overflow hw hNoOvf, Nat.sub_add_cancel hBnd.1]
  apply int_eq_of_intBalance_eq (intBalance_bvToInt hw (x - y))
    (intBalance_sub_of (intBalance_bvToInt hw x) (intBalance_bvToInt hw y))
  rw [Nat.add_comm H (Anneal.BitVecArith.signedKey y), ← Nat.add_assoc, hK]

private theorem bvToInt_signBit_nat {w : Nat} (hw : 0 < w) :
    bvToInt (Anneal.BitVecArith.signBit (w := w)) =
      Neg.neg (Int.ofNat (Nat.pow 2 (w - 1))) := by
  apply int_eq_of_intBalance_eq (intBalance_bvToInt hw _)
    (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat _))
  rw [signedKey_signBit hw]

/-- Exact `bvToInt` clamping formula for signed saturating addition. -/
theorem bvToInt_bvSaturatingAddSigned {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    bvToInt (bvSaturatingAddSigned x y) =
      if bvToInt x + bvToInt y < Neg.neg (Int.ofNat (Nat.pow 2 (w - 1))) then
        Neg.neg (Int.ofNat (Nat.pow 2 (w - 1)))
      else if Int.ofNat (Nat.pow 2 (w - 1)) ≤ bvToInt x + bvToInt y then
        Int.ofNat (Nat.pow 2 (w - 1) - 1)
      else
        bvToInt x + bvToInt y := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  have hBalSum := intBalance_add_of (intBalance_bvToInt hw x)
    (intBalance_bvToInt hw y)
  have hBalMin := intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H)
  have hBalMax := Anneal.InitLemmas.intBalance_ofNat H
  have hLtIff :
      bvToInt x + bvToInt y < Neg.neg (Int.ofNat H) ↔
        Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y < H := by
    rw [intBalance_lt_iff hBalSum hBalMin, Nat.zero_add]
    exact ⟨nat_lt_of_add_lt_add_right, fun h => Nat.add_lt_add_right h H⟩
  have hGeIff :
      Int.ofNat H ≤ bvToInt x + bvToInt y ↔
        H + Nat.pow 2 w ≤
          Anneal.BitVecArith.signedKey x + Anneal.BitVecArith.signedKey y := by
    rw [intBalance_le_iff hBalMax hBalSum, Nat.add_zero, hPow]
  unfold bvSaturatingAddSigned
  cases hOv : signedOverflowAddBv x y with
  | false =>
    have hB := (signedOverflowAddBv_eq_false_iff hw x y).1 hOv
    rw [bv_ite_bool_false_eq rfl,
      ite_false_of (fun h => Nat.not_le_of_gt (hLtIff.1 h) hB.1),
      ite_false_of (fun h => Nat.not_lt_of_ge (hGeIff.1 h) hB.2)]
    exact bvToInt_add_of_no_overflow hw hOv
  | true =>
    have hSk := signedKey_bvSaturatingAddSigned hw x y
    unfold bvSaturatingAddSigned at hSk
    rw [hOv] at hSk
    rw [bv_ite_bool_true_eq rfl]
    rw [bv_ite_bool_true_eq rfl] at hSk
    cases hmx : Anneal.BitVecArith.msb x with
    | true =>
      rw [hmx, bv_ite_bool_true_eq rfl] at hSk
      rw [bv_ite_bool_true_eq rfl]
      rw [signedKey_signBit hw] at hSk
      cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x +
          Anneal.BitVecArith.signedKey y) H with
      | inl hlt =>
        rw [ite_true_of (hLtIff.2 hlt)]
        exact bvToInt_signBit_nat hw
      | inr hge =>
        rw [ite_false_of (Nat.not_lt_of_ge hge)] at hSk
        cases Nat.lt_or_ge (H + Nat.pow 2 w)
            (Anneal.BitVecArith.signedKey x +
              Anneal.BitVecArith.signedKey y + 1) with
        | inl hhi =>
          have hhi' : H + Nat.pow 2 w ≤
              Anneal.BitVecArith.signedKey x +
                Anneal.BitVecArith.signedKey y := Nat.le_of_lt_succ hhi
          rw [ite_true_of hhi'] at hSk
          have hF : 0 < Nat.pow 2 w - 1 := by
            rw [hPow]
            have h1 := nat_two_pow_pos (w - 1)
            have h2 : 1 < H + H := Nat.lt_of_lt_of_le (by decide : 1 < 1 + 1)
              (Nat.add_le_add h1 h1)
            exact Nat.zero_lt_sub_of_lt h2
          rw [← hSk] at hF
          exact False.elim (Nat.lt_irrefl 0 hF)
        | inr hlo =>
          have hlo' : ¬ (H + Nat.pow 2 w ≤
              Anneal.BitVecArith.signedKey x +
                Anneal.BitVecArith.signedKey y) := fun h =>
            Nat.not_lt_of_ge hlo (Nat.lt_succ_of_le h)
          have hF := (signedOverflowAddBv_eq_false_iff hw x y).2
            ⟨hge, Nat.lt_of_not_le hlo'⟩
          rw [hF] at hOv
          nomatch hOv
    | false =>
      have hSame : Anneal.BitVecArith.msb x = Anneal.BitVecArith.msb y := by
        unfold signedOverflowAddBv at hOv
        exact of_decide_eq_true (bool_and_left hOv)
      rw [hmx, bv_ite_bool_false_eq rfl] at hSk
      rw [bv_ite_bool_false_eq rfl]
      have hkx := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
      have hmy : Anneal.BitVecArith.msb y = false := hSame.symm.trans hmx
      have hky := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
      have hgeH : H ≤ Anneal.BitVecArith.signedKey x +
          Anneal.BitVecArith.signedKey y := Nat.le_trans hkx (Nat.le_add_right _ _)
      have hgeHi : H + Nat.pow 2 w ≤ Anneal.BitVecArith.signedKey x +
          Anneal.BitVecArith.signedKey y := by
        cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x +
            Anneal.BitVecArith.signedKey y) (H + Nat.pow 2 w) with
        | inl hlt =>
          have hF := (signedOverflowAddBv_eq_false_iff hw x y).2 ⟨hgeH, hlt⟩
          rw [hF] at hOv
          nomatch hOv
        | inr hge => exact hge
      rw [ite_false_of (fun h => Nat.not_le_of_gt (hLtIff.1 h) hgeH),
        ite_true_of (hGeIff.2 hgeHi)]
      exact bvToInt_signedMaxBv hw

/-- Exact `bvToInt` clamping formula for signed saturating subtraction. -/
theorem bvToInt_bvSaturatingSubSigned {w : Nat} (hw : 0 < w)
    (x y : BitVec w) :
    bvToInt (bvSaturatingSubSigned x y) =
      if bvToInt x - bvToInt y < Neg.neg (Int.ofNat (Nat.pow 2 (w - 1))) then
        Neg.neg (Int.ofNat (Nat.pow 2 (w - 1)))
      else if Int.ofNat (Nat.pow 2 (w - 1)) ≤ bvToInt x - bvToInt y then
        Int.ofNat (Nat.pow 2 (w - 1) - 1)
      else
        bvToInt x - bvToInt y := by
  let H := Nat.pow 2 (w - 1)
  have hBalSub := intBalance_sub_of (intBalance_bvToInt hw x)
    (intBalance_bvToInt hw y)
  have hBalMin := intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H)
  have hBalMax := Anneal.InitLemmas.intBalance_ofNat H
  have hLtIff :
      bvToInt x - bvToInt y < Neg.neg (Int.ofNat H) ↔
        Anneal.BitVecArith.signedKey x + H < Anneal.BitVecArith.signedKey y := by
    have hH : Nat.pow 2 (w - 1) = H := rfl
    rw [intBalance_lt_iff hBalSub hBalMin, Nat.zero_add, hH,
      Nat.add_comm H (Anneal.BitVecArith.signedKey y)]
    exact ⟨nat_lt_of_add_lt_add_right, fun h => Nat.add_lt_add_right h H⟩
  have hGeIff :
      Int.ofNat H ≤ bvToInt x - bvToInt y ↔
        Anneal.BitVecArith.signedKey y + H ≤ Anneal.BitVecArith.signedKey x := by
    rw [intBalance_le_iff hBalMax hBalSub, Nat.add_zero,
      Nat.add_comm H (Anneal.BitVecArith.signedKey y),
      ← Nat.add_assoc H (Anneal.BitVecArith.signedKey y) H,
      Nat.add_comm H (Anneal.BitVecArith.signedKey y)]
    exact ⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h H⟩
  unfold bvSaturatingSubSigned
  cases hOv : signedOverflowSubBv x y with
  | false =>
    have hB := (signedOverflowSubBv_eq_false_iff hw x y).1 hOv
    rw [bv_ite_bool_false_eq rfl,
      ite_false_of (fun h => Nat.not_le_of_gt (hLtIff.1 h) hB.1),
      ite_false_of (fun h => Nat.not_lt_of_ge (hGeIff.1 h) hB.2)]
    exact bvToInt_sub_of_no_overflow hw hOv
  | true =>
    rw [bv_ite_bool_true_eq rfl]
    have hDiff : Anneal.BitVecArith.msb x ≠ Anneal.BitVecArith.msb y := by
      unfold signedOverflowSubBv at hOv
      exact bne_iff_ne.mp (bool_and_left hOv)
    cases hmx : Anneal.BitVecArith.msb x with
    | true =>
      have hmy : Anneal.BitVecArith.msb y = false := by
        cases hc : Anneal.BitVecArith.msb y with
        | false => rfl
        | true => exact False.elim (hDiff (hmx.trans hc.symm))
      have hkx := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmx
      have hky := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmy
      have hUdf : Anneal.BitVecArith.signedKey x + H <
          Anneal.BitVecArith.signedKey y := by
        cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x + H)
            (Anneal.BitVecArith.signedKey y) with
        | inl hlt => exact hlt
        | inr hge =>
          have hHi : Anneal.BitVecArith.signedKey x <
              Anneal.BitVecArith.signedKey y + H :=
            Nat.lt_of_lt_of_le hkx (Nat.le_trans (Nat.le_add_right H H)
              (Nat.add_le_add_right hky H))
          have hF := (signedOverflowSubBv_eq_false_iff hw x y).2 ⟨hge, hHi⟩
          rw [hF] at hOv
          nomatch hOv
      rw [bv_ite_bool_true_eq rfl, ite_true_of (hLtIff.2 hUdf)]
      exact bvToInt_signBit_nat hw
    | false =>
      have hmy : Anneal.BitVecArith.msb y = true := by
        cases hc : Anneal.BitVecArith.msb y with
        | true => rfl
        | false => exact False.elim (hDiff (hmx.trans hc.symm))
      have hkx := Anneal.BitVecArith.half_le_signedKey_of_msb_false hw hmx
      have hky := Anneal.BitVecArith.signedKey_lt_half_of_msb_true hw hmy
      have hNoUdf : Anneal.BitVecArith.signedKey y ≤
          Anneal.BitVecArith.signedKey x + H :=
        Nat.le_trans (Nat.le_of_lt hky) (Nat.le_trans hkx (Nat.le_add_right _ _))
      have hOvf : Anneal.BitVecArith.signedKey y + H ≤
          Anneal.BitVecArith.signedKey x := by
        cases Nat.lt_or_ge (Anneal.BitVecArith.signedKey x)
            (Anneal.BitVecArith.signedKey y + H) with
        | inr hge => exact hge
        | inl hlt =>
          have hF := (signedOverflowSubBv_eq_false_iff hw x y).2 ⟨hNoUdf, hlt⟩
          rw [hF] at hOv
          nomatch hOv
      rw [bv_ite_bool_false_eq rfl,
        ite_false_of (fun h => Nat.not_le_of_gt (hLtIff.1 h) hNoUdf),
        ite_true_of (hGeIff.2 hOvf)]
      exact bvToInt_signedMaxBv hw

/-- Non-overflow MIR agreement: `evalBinOp .add` on signed scalars matches
`bvSaturatingAddSigned` whenever `signedOverflowAddBv x y = false`. -/
theorem evalBinOp_add_eq_bvSaturatingAddSigned (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)}
    (hNoOvf : signedOverflowAddBv x y = false) :
    evalBinOp .add (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.scalar (bvToScalar w true (bvSaturatingAddSigned x y))) := by
  unfold bvSaturatingAddSigned
  rw [hNoOvf]
  exact evalBinOp_add_eq_add w true x y

/-- Full signed `evalBinOp .addWithOverflow` agreement for
`bvSaturatingAddSigned`. -/
theorem evalBinOp_addWithOverflow_saturating_signed (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ sum : BitVec (8 * w.byteSize), ∃ ovf : Bool,
      evalBinOp .addWithOverflow (.scalar (bvToScalar w true x))
          (.scalar (bvToScalar w true y)) =
        .ok (.tuple [.scalar (bvToScalar w true sum), .bool ovf]) ∧
      bvSaturatingAddSigned x y =
        if ovf then
          if Anneal.BitVecArith.msb x then
            Anneal.BitVecArith.signBit (w := 8 * w.byteSize)
          else signedMaxBv (8 * w.byteSize)
        else sum := by
  refine ⟨x + y, signedOverflowAddBv x y,
    evalBinOp_addWithOverflow_signed_eq w x y, rfl⟩

/-- Non-overflow MIR agreement: `evalBinOp .sub` on signed scalars matches
`bvSaturatingSubSigned` whenever `signedOverflowSubBv x y = false`. -/
theorem evalBinOp_sub_eq_bvSaturatingSubSigned (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)}
    (hNoOvf : signedOverflowSubBv x y = false) :
    evalBinOp .sub (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.scalar (bvToScalar w true (bvSaturatingSubSigned x y))) := by
  unfold bvSaturatingSubSigned
  rw [hNoOvf]
  exact evalBinOp_sub_eq_sub w true x y

/-- Full signed `evalBinOp .subWithOverflow` agreement for
`bvSaturatingSubSigned`. -/
theorem evalBinOp_subWithOverflow_saturating_signed (w : IntWidth)
    (x y : BitVec (8 * w.byteSize)) :
    ∃ diff : BitVec (8 * w.byteSize), ∃ ovf : Bool,
      evalBinOp .subWithOverflow (.scalar (bvToScalar w true x))
          (.scalar (bvToScalar w true y)) =
        .ok (.tuple [.scalar (bvToScalar w true diff), .bool ovf]) ∧
      bvSaturatingSubSigned x y =
        if ovf then
          if Anneal.BitVecArith.msb x then
            Anneal.BitVecArith.signBit (w := 8 * w.byteSize)
          else signedMaxBv (8 * w.byteSize)
        else diff := by
  refine ⟨x - y, signedOverflowSubBv x y,
    evalBinOp_subWithOverflow_signed_eq w x y, rfl⟩

/-- Unsigned exact-division admissibility predicate (`y ≠ 0 ∧ y ∣ x`). -/
@[expose] def ExactDivUnsigned {w : Nat} (x y : BitVec w) : Prop :=
  y.toNat ≠ 0 ∧ Nat.mod x.toNat y.toNat = 0

/-- Exact unsigned division inverse: when `y ∣ x`, `udiv x y * y = x`. -/
theorem bv_mul_udiv_of_exact {w : Nat} {x y : BitVec w}
    (hExact : ExactDivUnsigned x y) :
    Anneal.BitVec.mul (Anneal.BitVec.udiv x y) y = x := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_mul, Anneal.BitVec.toNat_udiv]
  have hEq : Nat.div x.toNat y.toNat * y.toNat = x.toNat := by
    have hda := nat_div_add_mod x.toNat y.toNat
    rw [hExact.2, Nat.add_zero, Nat.mul_comm] at hda
    exact hda
  rw [hEq]
  exact nat_mod_eq_of_lt x.isLt

/-- Right multiplicative cancellation for overflow-free unsigned products. -/
theorem udiv_mul_cancel_right {w : Nat} {q y : BitVec w}
    (hy : y.toNat ≠ 0) (hNoOvf : q.toNat * y.toNat < Nat.pow 2 w) :
    Anneal.BitVec.udiv (Anneal.BitVec.mul q y) y = q := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_udiv, Anneal.BitVec.toNat_mul,
    nat_mod_eq_of_lt hNoOvf, nat_mul_div_left _ (Nat.pos_of_ne_zero hy)]

/-- MIR `evalBinOp .div` followed by `evalBinOp .mul` recovers `x` under
`ExactDivUnsigned`. -/
theorem evalBinOp_div_mul_exact_unsigned (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)} (hExact : ExactDivUnsigned x y) :
    evalBinOp .div (.scalar (bvToScalar w false x))
        (.scalar (bvToScalar w false y)) =
      .ok (.scalar (bvToScalar w false (Anneal.BitVec.udiv x y))) ∧
    evalBinOp .mul
        (.scalar (bvToScalar w false (Anneal.BitVec.udiv x y)))
        (.scalar (bvToScalar w false y)) =
      .ok (.scalar (bvToScalar w false x)) := by
  refine ⟨evalBinOp_div_unsigned_eq_udiv x hExact.1, ?_⟩
  rw [evalBinOp_mul_eq_mul, bv_mul_udiv_of_exact hExact]

/-- Signed exact-division admissibility predicate (`y ≠ 0`, non-`INT_MIN / -1`,
and `|y| ∣ |x|`). -/
@[expose] def ExactDivSigned {w : Nat} (x y : BitVec w) : Prop :=
  y.toNat ≠ 0 ∧
  ¬ (x = Anneal.BitVecArith.signBit (w := w) ∧ y = Anneal.BitVec.allOnes w) ∧
  Nat.mod (bvAbs x).toNat (bvAbs y).toNat = 0

private theorem mul_neg_left {w : Nat} (a b : BitVec w) :
    Anneal.BitVec.mul (Anneal.BitVecArith.neg a) b =
      Anneal.BitVecArith.neg (Anneal.BitVec.mul a b) := by
  have hSum : Anneal.BitVec.mul (Anneal.BitVecArith.neg a) b +
      Anneal.BitVec.mul a b = BitVec.ofNat w 0 := by
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_mul,
      Anneal.BitVec.toNat_mul, Anneal.BitVecArith.toNat_neg,
      Anneal.BitVec.toNat_zero]
    cases ha : a.toNat with
    | zero =>
      rw [Nat.sub_zero, nat_mod_self, Nat.zero_mul, nat_zero_mod, Nat.add_zero,
        nat_zero_mod]
    | succ k =>
      have hMod : Nat.mod (Nat.pow 2 w - Nat.succ k) (Nat.pow 2 w) =
          Nat.pow 2 w - Nat.succ k := by
        apply nat_mod_eq_of_lt
        exact Nat.sub_lt (nat_two_pow_pos w) (Nat.zero_lt_succ k)
      rw [hMod]
      have haLt : Nat.succ k ≤ Nat.pow 2 w := by
        change k + 1 ≤ Nat.pow 2 w
        rw [← ha]
        exact Nat.le_of_lt (bitVec_toNat_lt_pow a)
      have hModSum :
          Nat.mod (Nat.mod ((Nat.pow 2 w - Nat.succ k) * b.toNat) (Nat.pow 2 w) +
            Nat.mod (Nat.succ k * b.toNat) (Nat.pow 2 w)) (Nat.pow 2 w) = 0 := by
        have h1 : ∀ u v m : Nat,
            Nat.mod (Nat.mod u m + Nat.mod v m) m = Nat.mod (u + v) m := by
          intro u v m
          have hu := nat_div_add_mod u m
          have hv := nat_div_add_mod v m
          have hSp : u + v = (Nat.mod u m + Nat.mod v m) +
              m * (Nat.div u m + Nat.div v m) := by
            rw [Nat.mul_add]
            have hL1 : u + v = (m * Nat.div u m + Nat.mod u m) +
                (m * Nat.div v m + Nat.mod v m) := by
              rw [hu, hv]
            rw [hL1, add_four_rearrange, Nat.add_comm (Nat.mod u m + Nat.mod v m)]
          have hC := congrArg (fun z => Nat.mod z m) hSp
          rw [nat_add_mul_mod_self_left] at hC
          exact hC.symm
        rw [h1, ← Nat.add_mul, Nat.sub_add_cancel haLt,
          nat_mul_mod_right]
      exact hModSum
  have h1 := congrArg (fun z => z + Anneal.BitVecArith.neg (Anneal.BitVec.mul a b))
    hSum
  have hAssoc : ∀ p q r : BitVec w, (p + q) + r = p + (q + r) := by
    intro p q r
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
      Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add]
    have hmL : ∀ u v m : Nat,
        Nat.mod (Nat.mod u m + v) m = Nat.mod (u + v) m := by
      intro u v m
      have hu := nat_div_add_mod u m
      have hSp : u + v = (Nat.mod u m + v) + m * Nat.div u m := by
        have h1' : u + v = (m * Nat.div u m + Nat.mod u m) + v := by rw [hu]
        rw [h1', Nat.add_assoc (m * Nat.div u m),
          Nat.add_comm (m * Nat.div u m)]
      have hC := congrArg (fun z => Nat.mod z m) hSp
      rw [nat_add_mul_mod_self_left] at hC
      exact hC.symm
    have hmR : ∀ u v m : Nat,
        Nat.mod (u + Nat.mod v m) m = Nat.mod (u + v) m := by
      intro u v m
      rw [Nat.add_comm u _, hmL, Nat.add_comm v u]
    rw [hmL, hmR, Nat.add_assoc]
  have hZeroL : ∀ p : BitVec w, BitVec.ofNat w 0 + p = p := by
    intro p
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.zero_add,
      nat_mod_eq_of_lt (bitVec_toNat_lt_pow p)]
  have hZeroR : ∀ p : BitVec w, p + BitVec.ofNat w 0 = p := by
    intro p
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.add_zero,
      nat_mod_eq_of_lt (bitVec_toNat_lt_pow p)]
  rw [hAssoc, Anneal.BitVecArith.add_neg_self, hZeroL, hZeroR] at h1
  exact h1

private theorem mul_comm_bv {w : Nat} (a b : BitVec w) :
    Anneal.BitVec.mul a b = Anneal.BitVec.mul b a := by
  apply Anneal.BitVec.eq_of_toNat_eq
  rw [Anneal.BitVec.toNat_mul, Anneal.BitVec.toNat_mul, Nat.mul_comm]

private theorem mul_neg_right {w : Nat} (a b : BitVec w) :
    Anneal.BitVec.mul a (Anneal.BitVecArith.neg b) =
      Anneal.BitVecArith.neg (Anneal.BitVec.mul a b) := by
  rw [mul_comm_bv a _, mul_neg_left, mul_comm_bv]

private theorem neg_neg_bv {w : Nat} (a : BitVec w) :
    Anneal.BitVecArith.neg (Anneal.BitVecArith.neg a) = a := by
  have hSum : Anneal.BitVecArith.neg (Anneal.BitVecArith.neg a) +
      Anneal.BitVecArith.neg a = BitVec.ofNat w 0 :=
    Anneal.BitVecArith.neg_add_self _
  have h1 := congrArg (fun z => z + a) hSum
  have hAssoc : ∀ p q r : BitVec w, (p + q) + r = p + (q + r) := by
    intro p q r
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add,
      Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_add]
    have hmL : ∀ u v m : Nat,
        Nat.mod (Nat.mod u m + v) m = Nat.mod (u + v) m := by
      intro u v m
      have hu := nat_div_add_mod u m
      have hSp : u + v = (Nat.mod u m + v) + m * Nat.div u m := by
        have h1' : u + v = (m * Nat.div u m + Nat.mod u m) + v := by rw [hu]
        rw [h1', Nat.add_assoc (m * Nat.div u m),
          Nat.add_comm (m * Nat.div u m)]
      have hC := congrArg (fun z => Nat.mod z m) hSp
      rw [nat_add_mul_mod_self_left] at hC
      exact hC.symm
    have hmR : ∀ u v m : Nat,
        Nat.mod (u + Nat.mod v m) m = Nat.mod (u + v) m := by
      intro u v m
      rw [Nat.add_comm u _, hmL, Nat.add_comm v u]
    rw [hmL, hmR, Nat.add_assoc]
  have hZeroL : ∀ p : BitVec w, BitVec.ofNat w 0 + p = p := by
    intro p
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.zero_add,
      nat_mod_eq_of_lt (bitVec_toNat_lt_pow p)]
  have hZeroR : ∀ p : BitVec w, p + BitVec.ofNat w 0 = p := by
    intro p
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_add, Anneal.BitVec.toNat_zero, Nat.add_zero,
      nat_mod_eq_of_lt (bitVec_toNat_lt_pow p)]
  rw [hAssoc, Anneal.BitVecArith.neg_add_self, hZeroR, hZeroL] at h1
  exact h1

/-- Signed exact division inverse: `bvSdiv x y * y = x` whenever `|y| ∣ |x|`
and `y ≠ 0`. -/
theorem bv_mul_bvSdiv_of_exact {w : Nat} {x y : BitVec w}
    (hExact : ExactDivSigned x y) :
    Anneal.BitVec.mul (bvSdiv x y) y = x := by
  have hyAbs : (bvAbs y).toNat ≠ 0 := by
    unfold bvAbs
    cases hm : Anneal.BitVecArith.msb y with
    | false =>
      rw [bv_ite_bool_false_eq rfl]
      exact hExact.1
    | true =>
      rw [bv_ite_bool_true_eq rfl]
      cases w with
      | zero =>
        exact False.elim (hExact.1 (Nat.eq_zero_of_le_zero
          (Nat.le_of_lt_succ y.isLt)))
      | succ w' =>
        have hyPos : 0 < y.toNat := Nat.pos_of_ne_zero hExact.1
        rw [Anneal.BitVecArith.toNat_neg_of_pos hyPos]
        exact Nat.ne_of_gt (Nat.zero_lt_sub_of_lt y.isLt)
  have hMag : Anneal.BitVec.mul (Anneal.BitVec.udiv (bvAbs x) (bvAbs y))
      (bvAbs y) = bvAbs x :=
    bv_mul_udiv_of_exact ⟨hyAbs, hExact.2.2⟩
  unfold bvSdiv
  cases hmx : Anneal.BitVecArith.msb x <;>
    cases hmy : Anneal.BitVecArith.msb y
  · have hxEq : bvAbs x = x := by
      unfold bvAbs; rw [hmx, bv_ite_bool_false_eq rfl]
    have hyEq : bvAbs y = y := by
      unfold bvAbs; rw [hmy, bv_ite_bool_false_eq rfl]
    rw [bv_ite_bool_false_eq (by decide : (false != false) = false), hxEq, hyEq]
    rw [hxEq, hyEq] at hMag
    exact hMag
  · have hxEq : bvAbs x = x := by
      unfold bvAbs; rw [hmx, bv_ite_bool_false_eq rfl]
    have hyEq : bvAbs y = Anneal.BitVecArith.neg y := by
      unfold bvAbs; rw [hmy, bv_ite_bool_true_eq rfl]
    rw [bv_ite_bool_true_eq (by decide : (false != true) = true), hxEq, hyEq]
    rw [hxEq, hyEq, mul_neg_right, ← mul_neg_left] at hMag
    exact hMag
  · have hxEq : bvAbs x = Anneal.BitVecArith.neg x := by
      unfold bvAbs; rw [hmx, bv_ite_bool_true_eq rfl]
    have hyEq : bvAbs y = y := by
      unfold bvAbs; rw [hmy, bv_ite_bool_false_eq rfl]
    rw [bv_ite_bool_true_eq (by decide : (true != false) = true), hxEq, hyEq]
    rw [hxEq, hyEq] at hMag
    have h1 := congrArg Anneal.BitVecArith.neg hMag
    rw [← mul_neg_left, neg_neg_bv] at h1
    exact h1
  · have hxEq : bvAbs x = Anneal.BitVecArith.neg x := by
      unfold bvAbs; rw [hmx, bv_ite_bool_true_eq rfl]
    have hyEq : bvAbs y = Anneal.BitVecArith.neg y := by
      unfold bvAbs; rw [hmy, bv_ite_bool_true_eq rfl]
    rw [bv_ite_bool_false_eq (by decide : (true != true) = false), hxEq, hyEq]
    rw [hxEq, hyEq, mul_neg_right] at hMag
    have h1 := congrArg Anneal.BitVecArith.neg hMag
    rw [neg_neg_bv, neg_neg_bv] at h1
    exact h1

private theorem bvToInt_pos_eq_ofNat {w : Nat} (hw : 0 < w) {x : BitVec w}
    (hmx : Anneal.BitVecArith.msb x = false) :
    bvToInt x = Int.ofNat x.toNat := by
  have hxLt := (Anneal.BitVecArith.msb_eq_false_iff hw x).1 hmx
  have h2 : 2 * x.toNat < Nat.pow 2 w := by
    rw [nat_two_pow_split hw, Nat.two_mul]
    exact Nat.add_lt_add hxLt hxLt
  unfold bvToInt
  rw [ite_true_of h2]

private theorem bvToInt_neg_eq_negSucc {w : Nat} (hw : 0 < w) {x : BitVec w}
    (hmx : Anneal.BitVecArith.msb x = true) :
    bvToInt x = Int.negSucc (Nat.pow 2 w - 1 - x.toNat) := by
  have hxGe := (Anneal.BitVecArith.msb_eq_true_iff hw x).1 hmx
  have hnot : ¬ (2 * x.toNat < Nat.pow 2 w) := by
    rw [nat_two_pow_split hw, Nat.two_mul]
    exact Nat.not_lt_of_ge (Nat.add_le_add hxGe hxGe)
  unfold bvToInt
  rw [ite_false_of hnot]
  have hDiff : Nat.pow 2 w - x.toNat = Nat.succ (Nat.pow 2 w - 1 - x.toNat) := by
    have hc := Nat.sub_add_cancel (Nat.zero_lt_sub_of_lt x.isLt)
    rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hc
    exact hc.symm
  rw [int_ofNat_sub_ofNat]
  unfold Int.subNatNat
  rw [hDiff]

private theorem bvAbs_toNat_eq_natAbs {W : Nat} (hW : 0 < W) (x : BitVec W) :
    (bvAbs x).toNat = (bvToInt x).natAbs := by
  unfold bvAbs
  cases hm : Anneal.BitVecArith.msb x with
  | false =>
    rw [bv_ite_bool_false_eq rfl, bvToInt_pos_eq_ofNat hW hm]
    rfl
  | true =>
    have hGe := (Anneal.BitVecArith.msb_eq_true_iff hW x).1 hm
    have hxPos : 0 < x.toNat := Nat.lt_of_lt_of_le (nat_two_pow_pos _) hGe
    rw [bv_ite_bool_true_eq rfl, Anneal.BitVecArith.toNat_neg_of_pos hxPos,
      bvToInt_neg_eq_negSucc hW hm]
    change Nat.pow 2 W - x.toNat = Nat.succ (Nat.pow 2 W - 1 - x.toNat)
    have hc := Nat.sub_add_cancel (Nat.zero_lt_sub_of_lt x.isLt)
    rw [Nat.sub_sub, Nat.add_comm x.toNat 1, ← Nat.sub_sub] at hc
    exact hc.symm

/-- Right multiplicative cancellation for overflow-free signed products. -/
theorem bvSdiv_mul_cancel_right {w : Nat} (hw : 0 < w) {q y : BitVec w}
    (hy : y.toNat ≠ 0) (hNoOvf : signedOverflowMulBv q y = false) :
    bvSdiv (Anneal.BitVec.mul q y) y = q := by
  let H := Nat.pow 2 (w - 1)
  have hPow : Nat.pow 2 w = H + H := nat_two_pow_split hw
  have hB := (signedOverflowMulBv_eq_false_iff hw q y).1 hNoOvf
  have hAbsQ : (bvAbs q).toNat = (bvToInt q).natAbs := bvAbs_toNat_eq_natAbs hw q
  have hAbsY : (bvAbs y).toNat = (bvToInt y).natAbs := bvAbs_toNat_eq_natAbs hw y
  have hyPos : 0 < (bvAbs y).toNat := by
    unfold bvAbs
    cases hm : Anneal.BitVecArith.msb y with
    | false => rw [bv_ite_bool_false_eq rfl]; exact Nat.pos_of_ne_zero hy
    | true =>
      rw [bv_ite_bool_true_eq rfl,
        Anneal.BitVecArith.toNat_neg_of_pos (Nat.pos_of_ne_zero hy)]
      exact Nat.zero_lt_sub_of_lt y.isLt
  have hNegQ : Anneal.BitVecArith.msb q = true →
      bvAbs q = Anneal.BitVecArith.neg q := by
    intro hm; unfold bvAbs; rw [bv_ite_bool_true_eq hm]
  have hPosQ : Anneal.BitVecArith.msb q = false → bvAbs q = q := by
    intro hm; unfold bvAbs; rw [bv_ite_bool_false_eq hm]
  have hNegY : Anneal.BitVecArith.msb y = true →
      bvAbs y = Anneal.BitVecArith.neg y := by
    intro hm; unfold bvAbs; rw [bv_ite_bool_true_eq hm]
  have hPosY : Anneal.BitVecArith.msb y = false → bvAbs y = y := by
    intro hm; unfold bvAbs; rw [bv_ite_bool_false_eq hm]
  cases hmq : Anneal.BitVecArith.msb q <;>
    cases hmy : Anneal.BitVecArith.msb y
  · have hqInt := bvToInt_pos_eq_ofNat hw hmq
    have hyInt := bvToInt_pos_eq_ofNat hw hmy
    rw [hqInt, hyInt] at hB
    have hMulInt : Int.ofNat q.toNat * Int.ofNat y.toNat =
        Int.ofNat (q.toNat * y.toNat) := rfl
    rw [hMulInt, int_ofNat_lt_iff] at hB
    have hProdLtW : q.toNat * y.toNat < Nat.pow 2 w := by
      rw [hPow]; exact Nat.lt_of_lt_of_le hB.2 (Nat.le_add_right H H)
    have hProdToNat : (Anneal.BitVec.mul q y).toNat = q.toNat * y.toNat := by
      rw [Anneal.BitVec.toNat_mul, nat_mod_eq_of_lt hProdLtW]
    have hmProd : Anneal.BitVecArith.msb (Anneal.BitVec.mul q y) = false :=
      (Anneal.BitVecArith.msb_eq_false_iff hw _).2 (by rw [hProdToNat]; exact hB.2)
    unfold bvSdiv
    rw [hmProd, hmy, bv_ite_bool_false_eq (by decide : (false != false) = false)]
    unfold bvAbs
    rw [bv_ite_bool_false_eq hmProd, bv_ite_bool_false_eq hmy]
    apply Anneal.BitVec.eq_of_toNat_eq
    rw [Anneal.BitVec.toNat_udiv, hProdToNat,
      nat_mul_div_left _ (Nat.pos_of_ne_zero hy)]
  · have hqInt := bvToInt_pos_eq_ofNat hw hmq
    have hProdMag : q.toNat * (bvAbs y).toNat ≤ H := by
      rw [bvToInt_neg_eq_negSucc hw hmy] at hAbsY
      rw [hAbsY]
      rw [hqInt, bvToInt_neg_eq_negSucc hw hmy] at hB
      have hyNatAbs : (Int.negSucc (Nat.pow 2 w - 1 - y.toNat)).natAbs =
          Nat.succ (Nat.pow 2 w - 1 - y.toNat) := rfl
      rw [hyNatAbs]
      have hMulNeg : Int.ofNat q.toNat *
          Int.negSucc (Nat.pow 2 w - 1 - y.toNat) =
          Neg.neg (Int.ofNat (q.toNat * Nat.succ (Nat.pow 2 w - 1 - y.toNat))) := by
        change Int.negOfNat (q.toNat * Nat.succ (Nat.pow 2 w - 1 - y.toNat)) = _
        rfl
      rw [hMulNeg] at hB
      have hBal := intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H))
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat
          (q.toNat * Nat.succ (Nat.pow 2 w - 1 - y.toNat))))
      rw [hBal, Nat.zero_add, Nat.zero_add] at hB
      exact hB.1
    cases hq0 : q.toNat with
    | zero =>
      have hqZero : q = BitVec.ofNat w 0 :=
        Anneal.BitVec.eq_of_toNat_eq (hq0.trans (Anneal.BitVec.toNat_zero w).symm)
      subst hqZero
      have hmZ : Anneal.BitVec.mul (BitVec.ofNat w 0) y = BitVec.ofNat w 0 := by
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_mul, Anneal.BitVec.toNat_zero, Nat.zero_mul,
          nat_zero_mod]
      rw [hmZ]
      unfold bvSdiv
      have hm0 : Anneal.BitVecArith.msb (BitVec.ofNat w 0) = false :=
        (Anneal.BitVecArith.msb_eq_false_iff hw _).2 (by
          rw [Anneal.BitVec.toNat_zero]; exact nat_two_pow_pos _)
      rw [hm0, hmy, bv_ite_bool_true_eq (by decide : (false != true) = true)]
      have hAbs0 : bvAbs (BitVec.ofNat w 0) = BitVec.ofNat w 0 := by
        unfold bvAbs; rw [bv_ite_bool_false_eq hm0]
      rw [hAbs0]
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVecArith.toNat_neg, Anneal.BitVec.toNat_udiv,
        Anneal.BitVec.toNat_zero, nat_zero_div, Nat.sub_zero, nat_mod_self]
    | succ q' =>
      have hProdPos : 0 < q.toNat * (bvAbs y).toNat :=
        Nat.mul_pos (by rw [hq0]; exact Nat.zero_lt_succ q') hyPos
      have hProdLtW : q.toNat * (bvAbs y).toNat < Nat.pow 2 w := by
        rw [hPow]
        exact Nat.lt_of_le_of_lt hProdMag
          (Nat.lt_add_of_pos_right (nat_two_pow_pos _))
      have hBvMul : Anneal.BitVec.mul q y =
          Anneal.BitVecArith.neg (BitVec.ofNat w (q.toNat * (bvAbs y).toNat)) := by
        have hY : y = Anneal.BitVecArith.neg (bvAbs y) := by
          rw [hNegY hmy, neg_neg_bv]
        have hMul : Anneal.BitVec.mul q y =
            Anneal.BitVec.mul q (Anneal.BitVecArith.neg (bvAbs y)) :=
          congrArg (Anneal.BitVec.mul q) hY
        rw [hMul, mul_neg_right]
        apply congrArg Anneal.BitVecArith.neg
        apply Anneal.BitVec.eq_of_toNat_eq
        rw [Anneal.BitVec.toNat_mul, Anneal.BitVec.toNat_ofNat]
      have hNegToNat : (Anneal.BitVec.mul q y).toNat =
          Nat.pow 2 w - q.toNat * (bvAbs y).toNat := by
        rw [hBvMul, Anneal.BitVecArith.toNat_neg_of_pos (by
          rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hProdLtW]
          exact hProdPos),
          Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hProdLtW]
      have hGeH : H ≤ (Anneal.BitVec.mul q y).toNat := by
        rw [hNegToNat, hPow]
        apply Nat.le_sub_of_add_le
        exact Nat.add_le_add_left hProdMag H
      have hmProd : Anneal.BitVecArith.msb (Anneal.BitVec.mul q y) = true :=
        (Anneal.BitVecArith.msb_eq_true_iff hw _).2 hGeH
      have hAbsProd : bvAbs (Anneal.BitVec.mul q y) =
          BitVec.ofNat w (q.toNat * (bvAbs y).toNat) := by
        have hUnf : bvAbs (Anneal.BitVec.mul q y) =
            if Anneal.BitVecArith.msb (Anneal.BitVec.mul q y) then
              Anneal.BitVecArith.neg (Anneal.BitVec.mul q y)
            else Anneal.BitVec.mul q y := rfl
        rw [hUnf, bv_ite_bool_true_eq hmProd, hBvMul, neg_neg_bv]
      unfold bvSdiv
      rw [hmProd, hmy, bv_ite_bool_false_eq (by decide : (true != true) = false),
        hAbsProd]
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_udiv, Anneal.BitVec.toNat_ofNat,
        nat_mod_eq_of_lt hProdLtW, nat_mul_div_left _ hyPos]
  · have hyInt := bvToInt_pos_eq_ofNat hw hmy
    have hProdMag : (bvAbs q).toNat * y.toNat ≤ H := by
      rw [bvToInt_neg_eq_negSucc hw hmq] at hAbsQ
      rw [hAbsQ]
      rw [hyInt, bvToInt_neg_eq_negSucc hw hmq] at hB
      have hqNatAbs : (Int.negSucc (Nat.pow 2 w - 1 - q.toNat)).natAbs =
          Nat.succ (Nat.pow 2 w - 1 - q.toNat) := rfl
      rw [hqNatAbs]
      have hMulNeg : Int.negSucc (Nat.pow 2 w - 1 - q.toNat) * Int.ofNat y.toNat =
          Neg.neg (Int.ofNat (Nat.succ (Nat.pow 2 w - 1 - q.toNat) * y.toNat)) := by
        cases hy0 : y.toNat with
        | zero => exact False.elim (hy hy0)
        | succ y' =>
          change Int.negOfNat (Nat.succ (Nat.pow 2 w - 1 - q.toNat) *
              Nat.succ y') = _
          rfl
      rw [hMulNeg] at hB
      have hBal := intBalance_le_iff
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat H))
        (intBalance_neg_of (Anneal.InitLemmas.intBalance_ofNat
          (Nat.succ (Nat.pow 2 w - 1 - q.toNat) * y.toNat)))
      rw [hBal, Nat.zero_add, Nat.zero_add] at hB
      exact hB.1
    have hqPosAbs : 0 < (bvAbs q).toNat := by
      rw [hNegQ hmq]
      have hGe := (Anneal.BitVecArith.msb_eq_true_iff hw q).1 hmq
      have hPos : 0 < q.toNat := Nat.lt_of_lt_of_le (nat_two_pow_pos _) hGe
      rw [Anneal.BitVecArith.toNat_neg_of_pos hPos]
      exact Nat.zero_lt_sub_of_lt q.isLt
    have hProdPos : 0 < (bvAbs q).toNat * y.toNat :=
      Nat.mul_pos hqPosAbs (Nat.pos_of_ne_zero hy)
    have hProdLtW : (bvAbs q).toNat * y.toNat < Nat.pow 2 w := by
      rw [hPow]
      exact Nat.lt_of_le_of_lt hProdMag
        (Nat.lt_add_of_pos_right (nat_two_pow_pos _))
    have hBvMul : Anneal.BitVec.mul q y =
        Anneal.BitVecArith.neg (BitVec.ofNat w ((bvAbs q).toNat * y.toNat)) := by
      have hQ : q = Anneal.BitVecArith.neg (bvAbs q) := by
        rw [hNegQ hmq, neg_neg_bv]
      have hMul : Anneal.BitVec.mul q y =
          Anneal.BitVec.mul (Anneal.BitVecArith.neg (bvAbs q)) y :=
        congrArg (fun a => Anneal.BitVec.mul a y) hQ
      rw [hMul, mul_neg_left]
      apply congrArg Anneal.BitVecArith.neg
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_mul, Anneal.BitVec.toNat_ofNat]
    have hNegToNat : (Anneal.BitVec.mul q y).toNat =
        Nat.pow 2 w - (bvAbs q).toNat * y.toNat := by
      rw [hBvMul, Anneal.BitVecArith.toNat_neg_of_pos (by
        rw [Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hProdLtW]
        exact hProdPos),
        Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hProdLtW]
    have hGeH : H ≤ (Anneal.BitVec.mul q y).toNat := by
      rw [hNegToNat, hPow]
      apply Nat.le_sub_of_add_le
      exact Nat.add_le_add_left hProdMag H
    have hmProd : Anneal.BitVecArith.msb (Anneal.BitVec.mul q y) = true :=
      (Anneal.BitVecArith.msb_eq_true_iff hw _).2 hGeH
    have hAbsProd : bvAbs (Anneal.BitVec.mul q y) =
        BitVec.ofNat w ((bvAbs q).toNat * y.toNat) := by
      have hUnf : bvAbs (Anneal.BitVec.mul q y) =
          if Anneal.BitVecArith.msb (Anneal.BitVec.mul q y) then
            Anneal.BitVecArith.neg (Anneal.BitVec.mul q y)
          else Anneal.BitVec.mul q y := rfl
      rw [hUnf, bv_ite_bool_true_eq hmProd, hBvMul, neg_neg_bv]
    unfold bvSdiv
    rw [hmProd, hmy, bv_ite_bool_true_eq (by decide : (true != false) = true),
      hAbsProd, hPosY hmy]
    have hUdiv : Anneal.BitVec.udiv (BitVec.ofNat w ((bvAbs q).toNat * y.toNat)) y =
        bvAbs q := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_udiv, Anneal.BitVec.toNat_ofNat,
        nat_mod_eq_of_lt hProdLtW, nat_mul_div_left _ (Nat.pos_of_ne_zero hy)]
    rw [hUdiv, hNegQ hmq, neg_neg_bv]
  · have hProdLt : (bvAbs q).toNat * (bvAbs y).toNat < H := by
      rw [bvToInt_neg_eq_negSucc hw hmq] at hAbsQ
      rw [bvToInt_neg_eq_negSucc hw hmy] at hAbsY
      have hqNatAbs : (bvAbs q).toNat =
          Nat.succ (Nat.pow 2 w - 1 - q.toNat) := hAbsQ
      have hyNatAbs : (bvAbs y).toNat =
          Nat.succ (Nat.pow 2 w - 1 - y.toNat) := hAbsY
      rw [bvToInt_neg_eq_negSucc hw hmq,
        bvToInt_neg_eq_negSucc hw hmy] at hB
      have hMulPos :
          Int.negSucc (Nat.pow 2 w - 1 - q.toNat) *
            Int.negSucc (Nat.pow 2 w - 1 - y.toNat) =
            Int.ofNat
              (Nat.succ (Nat.pow 2 w - 1 - q.toNat) *
                Nat.succ (Nat.pow 2 w - 1 - y.toNat)) := rfl
      rw [hMulPos, int_ofNat_lt_iff, ← hqNatAbs, ← hyNatAbs] at hB
      exact hB.2
    have hProdLtW : (bvAbs q).toNat * (bvAbs y).toNat < Nat.pow 2 w := by
      rw [hPow]
      exact Nat.lt_of_lt_of_le hProdLt (Nat.le_add_right H H)
    have hBvMul : Anneal.BitVec.mul q y =
        BitVec.ofNat w ((bvAbs q).toNat * (bvAbs y).toNat) := by
      have hQ : q = Anneal.BitVecArith.neg (bvAbs q) := by
        rw [hNegQ hmq, neg_neg_bv]
      have hY : y = Anneal.BitVecArith.neg (bvAbs y) := by
        rw [hNegY hmy, neg_neg_bv]
      have hMul1 : Anneal.BitVec.mul q y =
          Anneal.BitVec.mul (Anneal.BitVecArith.neg (bvAbs q))
            (Anneal.BitVecArith.neg (bvAbs y)) :=
        Eq.trans (congrArg (fun a => Anneal.BitVec.mul a y) hQ)
          (congrArg (Anneal.BitVec.mul (Anneal.BitVecArith.neg (bvAbs q))) hY)
      have hMul : Anneal.BitVec.mul q y =
          Anneal.BitVec.mul (bvAbs q) (bvAbs y) := by
        rw [hMul1, mul_neg_left, mul_neg_right, neg_neg_bv]
      rw [hMul]
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_mul, Anneal.BitVec.toNat_ofNat]
    have hProdToNat : (Anneal.BitVec.mul q y).toNat =
        (bvAbs q).toNat * (bvAbs y).toNat := by
      rw [hBvMul, Anneal.BitVec.toNat_ofNat, nat_mod_eq_of_lt hProdLtW]
    have hmProd : Anneal.BitVecArith.msb (Anneal.BitVec.mul q y) = false :=
      (Anneal.BitVecArith.msb_eq_false_iff hw _).2
        (by rw [hProdToNat]; exact hProdLt)
    have hAbsProd : bvAbs (Anneal.BitVec.mul q y) = Anneal.BitVec.mul q y := by
      unfold bvAbs; rw [bv_ite_bool_false_eq hmProd]
    unfold bvSdiv
    rw [hmProd, hmy, bv_ite_bool_true_eq (by decide : (false != true) = true),
      hAbsProd]
    have hUdiv :
        Anneal.BitVec.udiv (Anneal.BitVec.mul q y) (bvAbs y) = bvAbs q := by
      apply Anneal.BitVec.eq_of_toNat_eq
      rw [Anneal.BitVec.toNat_udiv, hProdToNat, nat_mul_div_left _ hyPos]
    rw [hUdiv, hNegQ hmq, neg_neg_bv]

/-- MIR `evalBinOp .div` followed by `evalBinOp .mul` recovers `x` under
`ExactDivSigned`. -/
theorem evalBinOp_div_mul_exact_signed (w : IntWidth)
    {x y : BitVec (8 * w.byteSize)} (hExact : ExactDivSigned x y) :
    evalBinOp .div (.scalar (bvToScalar w true x))
        (.scalar (bvToScalar w true y)) =
      .ok (.scalar (bvToScalar w true (bvSdiv x y))) ∧
    evalBinOp .mul
        (.scalar (bvToScalar w true (bvSdiv x y)))
        (.scalar (bvToScalar w true y)) =
      .ok (.scalar (bvToScalar w true x)) := by
  refine ⟨evalBinOp_div_signed_eq w hExact.1 hExact.2.1, ?_⟩
  rw [evalBinOp_mul_eq_mul, bv_mul_bvSdiv_of_exact hExact]

/-! ## Part 5: Typed Scalar List Codecs over `ListChunks.chunksOf` -/

/-- Encode a single `BitVec (8 * w.byteSize)` into `w.byteSize` raw bytes
according to `endian`. -/
@[expose] noncomputable def encodeBvChunk (endian : TargetEndian) (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) : List (BitVec 8) :=
  match endian with
  | .little => Anneal.LeBytes.toLeBytes w.byteSize (toLeWidth x)
  | .big => Anneal.LeBytes.toBeBytes w.byteSize (toLeWidth x)

/-- Decode a chunk of bytes into `BitVec (8 * w.byteSize)` according to
`endian`. -/
@[expose] noncomputable def decodeBvChunk (endian : TargetEndian) (w : IntWidth)
    (bs : List (BitVec 8)) : BitVec (8 * w.byteSize) :=
  BitVec.ofNat (8 * w.byteSize)
    (match endian with
    | .little => Anneal.LeBytes.fromLeBytes bs
    | .big => Anneal.LeBytes.fromBeBytes bs)

/-- Every encoded chunk has exact byte length `w.byteSize`. -/
theorem length_encodeBvChunk (endian : TargetEndian) (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    (encodeBvChunk endian w x).length = w.byteSize := by
  cases endian with
  | little => exact Anneal.LeBytes.toLeBytes_length w.byteSize (toLeWidth x)
  | big => exact Anneal.LeBytes.toBeBytes_length w.byteSize (toLeWidth x)

/-- Single-element round-trip: `decodeBvChunk` inverts `encodeBvChunk`. -/
@[simp] theorem decodeBvChunk_encodeBvChunk (endian : TargetEndian) (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) :
    decodeBvChunk endian w (encodeBvChunk endian w x) = x := by
  unfold decodeBvChunk encodeBvChunk
  cases endian with
  | little =>
    dsimp only
    rw [Anneal.LeBytes.fromLeBytes_toLeBytes, toNat_toLeWidth, ofNat_toNat_self]
  | big =>
    dsimp only
    rw [Anneal.LeBytes.fromBeBytes_toBeBytes, toNat_toLeWidth, ofNat_toNat_self]

/-- Right inverse for any chunk whose byte length equals `w.byteSize`. -/
theorem encodeBvChunk_decodeBvChunk_of_length (endian : TargetEndian)
    (w : IntWidth) {bs : List (BitVec 8)} (hlen : bs.length = w.byteSize) :
    encodeBvChunk endian w (decodeBvChunk endian w bs) = bs := by
  unfold decodeBvChunk encodeBvChunk
  cases endian with
  | little =>
    dsimp only
    have hdecLt : Anneal.LeBytes.fromLeBytes bs <
        Nat.pow 2 (8 * w.byteSize) := by
      rw [← hlen, Nat.mul_comm 8 bs.length]
      exact Anneal.LeBytes.fromLeBytes_lt bs
    unfold Anneal.LeBytes.toLeBytes
    rw [toNat_toLeWidth, Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt hdecLt, ← hlen]
    exact Anneal.LeBytes.toLeBytesAux_fromLeBytes bs
  | big =>
    dsimp only
    have hdecLt : Anneal.LeBytes.fromBeBytes bs <
        Nat.pow 2 (8 * w.byteSize) := by
      rw [← hlen, Nat.mul_comm 8 bs.length]
      unfold Anneal.LeBytes.fromBeBytes
      have h1 := Anneal.LeBytes.fromLeBytes_lt bs.reverse
      rw [list_length_reverse] at h1
      exact h1
    unfold Anneal.LeBytes.toBeBytes Anneal.LeBytes.toLeBytes
    rw [toNat_toLeWidth, Anneal.BitVec.toNat_ofNat,
      nat_mod_eq_of_lt hdecLt]
    unfold Anneal.LeBytes.fromBeBytes
    have hL : bs.reverse.length = w.byteSize := by
      rw [list_length_reverse, hlen]
    rw [← hL, Anneal.LeBytes.toLeBytesAux_fromLeBytes, list_reverse_reverse]

/-- Serialize a list of `w`-bit scalars into contiguous raw bytes. -/
@[expose] noncomputable def encodeBvListBytes (endian : TargetEndian) (w : IntWidth)
    (xs : List (BitVec (8 * w.byteSize))) : List (BitVec 8) :=
  (xs.map (encodeBvChunk endian w)).flatten

/-- Deserialize a contiguous byte list into fixed-width
`BitVec (8 * w.byteSize)` elements by partitioning at stride `w.byteSize`. -/
@[expose] noncomputable def decodeBvListBytes (endian : TargetEndian) (w : IntWidth)
    (bs : List (BitVec 8)) : List (BitVec (8 * w.byteSize)) :=
  (Anneal.ListChunks.chunksOf w.byteSize bs).map (decodeBvChunk endian w)

/-- Unfolding equations for `encodeBvListBytes`. -/
@[simp] theorem encodeBvListBytes_nil (endian : TargetEndian) (w : IntWidth) :
    encodeBvListBytes endian w [] = [] := rfl

/-- Step equation for `encodeBvListBytes` on `x :: xs`. -/
@[simp] theorem encodeBvListBytes_cons (endian : TargetEndian) (w : IntWidth)
    (x : BitVec (8 * w.byteSize)) (xs : List (BitVec (8 * w.byteSize))) :
    encodeBvListBytes endian w (x :: xs) =
      encodeBvChunk endian w x ++ encodeBvListBytes endian w xs :=
  rfl

/-- Append distributivity for `encodeBvListBytes`. -/
theorem encodeBvListBytes_append (endian : TargetEndian) (w : IntWidth)
    (xs ys : List (BitVec (8 * w.byteSize))) :
    encodeBvListBytes endian w (xs ++ ys) =
      encodeBvListBytes endian w xs ++ encodeBvListBytes endian w ys := by
  unfold encodeBvListBytes
  rw [list_map_append, list_flatten_append]

/-- Byte-length preservation: `(encodeBvListBytes endian w xs).length =
xs.length * w.byteSize`. -/
theorem length_encodeBvListBytes (endian : TargetEndian) (w : IntWidth) :
    ∀ xs : List (BitVec (8 * w.byteSize)),
      (encodeBvListBytes endian w xs).length = xs.length * w.byteSize
  | [] => by
    rw [encodeBvListBytes_nil]
    exact (Nat.zero_mul w.byteSize).symm
  | x :: rest => by
    rw [encodeBvListBytes_cons, List.length_append, length_encodeBvChunk,
      length_encodeBvListBytes endian w rest, List.length_cons]
    have hMul : (rest.length + 1) * w.byteSize =
        rest.length * w.byteSize + w.byteSize :=
      Nat.succ_mul rest.length w.byteSize
    rw [hMul, Nat.add_comm w.byteSize (rest.length * w.byteSize)]

/-- Partitioning `encodeBvListBytes endian w xs` into `w.byteSize`-byte chunks
recovers each element's encoded byte slice exactly. -/
theorem chunksOf_encodeBvListBytes (endian : TargetEndian) (w : IntWidth) :
    ∀ xs : List (BitVec (8 * w.byteSize)),
      Anneal.ListChunks.chunksOf w.byteSize (encodeBvListBytes endian w xs) =
        xs.map (encodeBvChunk endian w)
  | [] => by
    rw [encodeBvListBytes_nil, Anneal.ListChunks.chunksOf_nil, List.map_nil]
  | x :: rest => by
    have hpos : 0 < w.byteSize := intWidth_byteSize_pos w
    have hlen : (encodeBvChunk endian w x).length = w.byteSize :=
      length_encodeBvChunk endian w x
    have hdiv : Nat.mod (encodeBvChunk endian w x).length w.byteSize = 0 := by
      rw [hlen, nat_mod_self]
    have hSingle :
        Anneal.ListChunks.chunksOf w.byteSize (encodeBvChunk endian w x) =
          [encodeBvChunk endian w x] := by
      cases hc : encodeBvChunk endian w x with
      | nil =>
        rw [hc, List.length_nil] at hlen
        rw [← hlen] at hpos
        exact False.elim (Nat.lt_irrefl 0 hpos)
      | cons b bs =>
        have hdrop0 : (b :: bs).drop w.byteSize = [] := by
          apply list_eq_nil_of_length_eq_zero
          rw [list_length_drop, ← hc, hlen, Nat.sub_self]
        have htake : (b :: bs).take w.byteSize = b :: bs := by
          apply list_take_of_length_le
          rw [← hc, hlen]
          exact Nat.le_refl _
        rw [Anneal.ListChunks.chunksOf_cons hpos, htake, hdrop0,
          Anneal.ListChunks.chunksOf_nil]
    rw [encodeBvListBytes_cons,
      Anneal.ListChunks.chunksOf_append_exact hpos _ _ hdiv,
      hSingle, chunksOf_encodeBvListBytes endian w rest, List.map_cons]
    rfl

/-- List codec left inverse: `decodeBvListBytes` recovers `xs` verbatim across
both `.little` and `.big` `TargetEndian`. -/
@[simp] theorem decodeBvListBytes_encodeBvListBytes (endian : TargetEndian)
    (w : IntWidth) (xs : List (BitVec (8 * w.byteSize))) :
    decodeBvListBytes endian w (encodeBvListBytes endian w xs) = xs := by
  unfold decodeBvListBytes
  rw [chunksOf_encodeBvListBytes, list_map_map]
  have hId : ∀ ys : List (BitVec (8 * w.byteSize)),
      ys.map (fun x => decodeBvChunk endian w (encodeBvChunk endian w x)) = ys := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y rest ih =>
      rw [List.map_cons, decodeBvChunk_encodeBvChunk, ih]
  exact hId xs

/-- Injectivity of `encodeBvListBytes`. -/
theorem encodeBvListBytes_injective {endian : TargetEndian} {w : IntWidth}
    {xs ys : List (BitVec (8 * w.byteSize))}
    (h : encodeBvListBytes endian w xs = encodeBvListBytes endian w ys) :
    xs = ys := by
  rw [← decodeBvListBytes_encodeBvListBytes endian w xs,
    ← decodeBvListBytes_encodeBvListBytes endian w ys, h]

/-- Right inverse for any byte buffer whose length is a multiple of
`w.byteSize`. -/
theorem encodeBvListBytes_decodeBvListBytes_of_mod_eq_zero (endian : TargetEndian)
    (w : IntWidth) {bs : List (BitVec 8)}
    (hmod : Nat.mod bs.length w.byteSize = 0) :
    encodeBvListBytes endian w (decodeBvListBytes endian w bs) = bs := by
  have hpos : 0 < w.byteSize := intWidth_byteSize_pos w
  have hFull : ∀ (n : Nat) (xs : List (BitVec 8)),
      xs.length ≤ n → Nat.mod xs.length w.byteSize = 0 →
      ((Anneal.ListChunks.chunksOf w.byteSize xs).map
        (fun c => encodeBvChunk endian w (decodeBvChunk endian w c))).flatten =
        xs := by
    intro n
    induction n with
    | zero =>
      intro xs hle _
      cases xs with
      | nil =>
        rw [Anneal.ListChunks.chunksOf_nil]
        rfl
      | cons _ _ => exact False.elim (Nat.not_succ_le_zero _ hle)
    | succ n ih =>
      intro xs hle hxmod
      cases xs with
      | nil =>
        rw [Anneal.ListChunks.chunksOf_nil]
        rfl
      | cons b rest =>
        have hlenLe : w.byteSize ≤ (b :: rest).length := by
          cases Nat.lt_or_ge (b :: rest).length w.byteSize with
          | inl hlt =>
            rw [nat_mod_eq_of_lt hlt] at hxmod
            nomatch hxmod
          | inr hge => exact hge
        have hTakeLen : ((b :: rest).take w.byteSize).length = w.byteSize :=
          list_length_take_of_le (b :: rest) w.byteSize hlenLe
        have hDropLen : ((b :: rest).drop w.byteSize).length ≤ n := by
          rw [List.length_cons] at hle
          rw [list_length_drop, List.length_cons]
          cases hsz : w.byteSize with
          | zero => rw [hsz] at hpos; exact False.elim (Nat.lt_irrefl 0 hpos)
          | succ s' =>
            rw [Nat.succ_sub_succ]
            exact Nat.le_trans (Nat.sub_le rest.length s')
              (Nat.le_of_succ_le_succ hle)
        have hDropMod :
            Nat.mod ((b :: rest).drop w.byteSize).length w.byteSize = 0 := by
          rw [list_length_drop]
          have hSub : (b :: rest).length - w.byteSize + w.byteSize =
              (b :: rest).length := Nat.sub_add_cancel hlenLe
          have hC := congrArg (fun z => Nat.mod z w.byteSize) hSub
          rw [nat_add_mod_left, hxmod] at hC
          exact hC
        rw [Anneal.ListChunks.chunksOf_cons hpos, List.map_cons,
          list_flatten_cons, encodeBvChunk_decodeBvChunk_of_length endian w hTakeLen,
          ih ((b :: rest).drop w.byteSize) hDropLen hDropMod]
        exact list_take_append_drop (b :: rest) w.byteSize
  unfold encodeBvListBytes decodeBvListBytes
  rw [list_map_map]
  exact hFull bs.length bs (Nat.le_refl bs.length) hmod

/-- Lift a scalar list directly into initialized MIR memory bytes (`AllocByte`)
with provenance `prov`. -/
@[expose] noncomputable def encodeScalarListAllocBytes (endian : TargetEndian) (w : IntWidth)
    (prov : Option AllocId) (xs : List (BitVec (8 * w.byteSize))) :
    List AllocByte :=
  (encodeBvListBytes endian w xs).map (allocByteOfBv prov)

/-- Every byte emitted by `encodeScalarListAllocBytes` is initialized. -/
theorem allBytesInit_encodeScalarListAllocBytes (endian : TargetEndian)
    (w : IntWidth) (prov : Option AllocId)
    (xs : List (BitVec (8 * w.byteSize))) :
    allBytesInit (encodeScalarListAllocBytes endian w prov xs) = true :=
  allBytesInit_map_allocByteOfBv prov (encodeBvListBytes endian w xs)

/-- Extracting initialized `BitVec 8` bytes from `encodeScalarListAllocBytes`
recovers `encodeBvListBytes` and decodes cleanly back to `xs`. -/
theorem decodeBvListBytes_extractInitBvBytes_encodeScalarList (endian : TargetEndian)
    (w : IntWidth) (prov : Option AllocId)
    (xs : List (BitVec (8 * w.byteSize))) :
    extractInitBvBytes (encodeScalarListAllocBytes endian w prov xs) =
        encodeBvListBytes endian w xs ∧
      decodeBvListBytes endian w
          (extractInitBvBytes (encodeScalarListAllocBytes endian w prov xs)) =
        xs := by
  have hExt :
      extractInitBvBytes (encodeScalarListAllocBytes endian w prov xs) =
        encodeBvListBytes endian w xs :=
    extractInitBvBytes_map_allocByteOfBv prov (encodeBvListBytes endian w xs)
  refine ⟨hExt, ?_⟩
  rw [hExt, decodeBvListBytes_encodeBvListBytes]

/-- MIR `decodeVal` equivalence on serialized scalar arrays: chunking
`encodeScalarListAllocBytes endian w none xs` and decoding each `w.byteSize`
slice with `decodeVal endian (.int w s)` recovers every `bvToScalar w s x`. -/
theorem chunksOf_decodeVal_encodeScalarList (endian : TargetEndian)
    (w : IntWidth) (s : Bool) (xs : List (BitVec (8 * w.byteSize))) :
    (Anneal.ListChunks.chunksOf w.byteSize
        (encodeScalarListAllocBytes endian w none xs)).map
        (decodeVal endian (.int w s)) =
      xs.map (fun x => .ok (some (.scalar (bvToScalar w s x)))) := by
  have hpos : 0 < w.byteSize := intWidth_byteSize_pos w
  have hChunks :
      Anneal.ListChunks.chunksOf w.byteSize
          (encodeScalarListAllocBytes endian w none xs) =
        (Anneal.ListChunks.chunksOf w.byteSize
            (encodeBvListBytes endian w xs)).map
          (fun chunk => chunk.map (allocByteOfBv none)) := by
    unfold encodeScalarListAllocBytes
    induction xs with
    | nil =>
      rw [encodeBvListBytes_nil, List.map_nil,
        Anneal.ListChunks.chunksOf_nil, Anneal.ListChunks.chunksOf_nil,
        List.map_nil]
    | cons x rest ih =>
      have hlen : (encodeBvChunk endian w x).length = w.byteSize :=
        length_encodeBvChunk endian w x
      have hdiv : Nat.mod (encodeBvChunk endian w x).length w.byteSize = 0 := by
        rw [hlen, nat_mod_self]
      have hdivMap : Nat.mod ((encodeBvChunk endian w x).map
          (allocByteOfBv none)).length w.byteSize = 0 := by
        rw [list_length_map, hdiv]
      have hSingle :
          Anneal.ListChunks.chunksOf w.byteSize (encodeBvChunk endian w x) =
            [encodeBvChunk endian w x] := by
        cases hc : encodeBvChunk endian w x with
        | nil =>
          rw [hc, List.length_nil] at hlen
          rw [← hlen] at hpos
          exact False.elim (Nat.lt_irrefl 0 hpos)
        | cons b bs =>
          have hdrop0 : (b :: bs).drop w.byteSize = [] := by
            apply list_eq_nil_of_length_eq_zero
            rw [list_length_drop, ← hc, hlen, Nat.sub_self]
          have htake : (b :: bs).take w.byteSize = b :: bs := by
            apply list_take_of_length_le
            rw [← hc, hlen]
            exact Nat.le_refl _
          rw [Anneal.ListChunks.chunksOf_cons hpos, htake, hdrop0,
            Anneal.ListChunks.chunksOf_nil]
      have hSingleMap :
          Anneal.ListChunks.chunksOf w.byteSize
              ((encodeBvChunk endian w x).map (allocByteOfBv none)) =
            [(encodeBvChunk endian w x).map (allocByteOfBv none)] := by
        cases hc : encodeBvChunk endian w x with
        | nil =>
          rw [hc, List.length_nil] at hlen
          rw [← hlen] at hpos
          exact False.elim (Nat.lt_irrefl 0 hpos)
        | cons b bs =>
          have hdrop0 :
              ((b :: bs).map (allocByteOfBv none)).drop w.byteSize = [] := by
            apply list_eq_nil_of_length_eq_zero
            rw [list_length_drop, list_length_map, ← hc, hlen, Nat.sub_self]
          have htake :
              ((b :: bs).map (allocByteOfBv none)).take w.byteSize =
                (b :: bs).map (allocByteOfBv none) := by
            apply list_take_of_length_le
            rw [list_length_map, ← hc, hlen]
            exact Nat.le_refl _
          rw [List.map_cons, Anneal.ListChunks.chunksOf_cons hpos, ← List.map_cons,
            htake, hdrop0, Anneal.ListChunks.chunksOf_nil]
      rw [encodeBvListBytes_cons, list_map_append,
        Anneal.ListChunks.chunksOf_append_exact hpos _ _ hdivMap,
        Anneal.ListChunks.chunksOf_append_exact hpos _ _ hdiv,
        hSingleMap, hSingle, ih, list_map_append, List.map_cons, List.map_nil]
  rw [hChunks, chunksOf_encodeBvListBytes, list_map_map, list_map_map]
  have hElem : ∀ x : BitVec (8 * w.byteSize),
      decodeVal endian (.int w s)
          ((encodeBvChunk endian w x).map (allocByteOfBv none)) =
        .ok (some (.scalar (bvToScalar w s x))) := by
    intro x
    let ⟨bytes, hEnc, hDec⟩ := decodeVal_encodeVal_bvToScalar endian w s x
    rw [encodeVal_bvToScalar] at hEnc
    have hMapEq : (encodeBvChunk endian w x).map (allocByteOfBv none) = bytes := by
      injection hEnc with hBytes
      rw [← hBytes]
      have hU : (encodeBvChunk endian w x).map UInt8.ofBitVec =
          encodeUInt endian w.byteSize x.toNat := by
        have hToNat : encodeUInt endian w.byteSize x.toNat =
            encodeUInt endian w.byteSize (toLeWidth x).toNat := rfl
        rw [hToNat]
        unfold encodeBvChunk
        cases endian with
        | little =>
          exact (encodeUInt_little_eq_toLeBytes w.byteSize (toLeWidth x)).symm
        | big =>
          exact (encodeUInt_big_eq_toBeBytes w.byteSize (toLeWidth x)).symm
      rw [← hU, list_map_map]
      rfl
    rw [hMapEq]
    exact hDec
  have hCongr : ∀ ys : List (BitVec (8 * w.byteSize)),
      ys.map (fun x => decodeVal endian (.int w s)
          ((encodeBvChunk endian w x).map (allocByteOfBv none))) =
        ys.map (fun x => .ok (some (.scalar (bvToScalar w s x)))) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y rest ih =>
      rw [List.map_cons, List.map_cons, hElem y, ih]
  exact hCongr xs

end Anneal.Core

end
