-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import ProductionPaths
import Init.ByCases
import Init.Data.BitVec.Bootstrap
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Option.Lemmas
import Init.Omega
import Init.Tactics

@[expose] public section

namespace ProductionEndpoints

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction SymExec ProductionPaths

/-!
`ProductionPaths` turns any word that a control path returns into a safe
actual return. These fixed endpoints require every path to return a word
that implements endianness conversion, bit by bit, so a mutated
implementation can still prove its executions while failing this bridge to
the unchanged specification.
-/

/-- Expected bit sources of the byte reversal within `bits`. -/
def revSrc (bits i : Nat) : BitSrc :=
  if i < bits then .input (reverseByteIndex bits i) else .zero

/-- Expected bit sources of the input masked to `bits`. -/
def maskSrc (bits i : Nat) : BitSrc :=
  if i < bits then .input i else .zero

theorem bigEndian_bits : ∀ width : Fin 4,
    (pathWord true width.val).any
      (fun s => s.bitsAre (revSrc (8 * 2 ^ width.val))) = true := by
  refine fin4_cases ?_ ?_ ?_ ?_ <;> decide +kernel

theorem littleEndian_bits : ∀ width : Fin 4,
    (pathWord false width.val).any
      (fun s => s.bitsAre (maskSrc (8 * 2 ^ width.val))) = true := by
  refine fin4_cases ?_ ?_ ?_ ?_ <;> decide +kernel

theorem byteReversal_of_bitsAre {s : Sym} {bits : Nat}
    (h : s.bitsAre (revSrc bits) = true) (x : Word) :
    ByteReversal bits x (s.eval x) := by
  intro i hi
  have hb := Sym.bitsAre_sound h x i hi
  unfold revSrc at hb
  by_cases hbits : i < bits
  · simp only [hbits, ↓reduceIte, BitSrc.Agrees] at hb ⊢
    exact hb
  · simp only [hbits, ↓reduceIte, BitSrc.Agrees] at hb ⊢
    exact hb

theorem eq_mask_of_bitsAre {s : Sym} {bits : Nat}
    (h : s.bitsAre (maskSrc bits) = true) (x : Word) :
    s.eval x = x &&& BitVec.ofNat 64 (2 ^ bits - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := Sym.bitsAre_sound h x i hi
  unfold maskSrc at hb
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hbits : i < bits
  · simp only [hbits, ↓reduceIte, BitSrc.Agrees] at hb
    simp only [hb, hi, hbits, decide_true, Bool.and_true]
  · simp only [hbits, ↓reduceIte, BitSrc.Agrees] at hb
    simp only [hb, hbits, decide_false, Bool.and_false]

theorem bigEndian (width : Fin 4) : ∃ s : Sym,
    pathWord true width.val = some s ∧
      ∀ x, ByteReversal (8 * 2 ^ width.val) x (s.eval x) :=
  let ⟨s, hp, hb⟩ := (Option.any_eq_true _ _).mp (bigEndian_bits width)
  ⟨s, hp, byteReversal_of_bitsAre hb⟩

theorem littleEndian (width : Fin 4) : ∃ s : Sym,
    pathWord false width.val = some s ∧
      ∀ x, s.eval x =
        x &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) :=
  let ⟨s, hp, hb⟩ := (Option.any_eq_true _ _).mp (littleEndian_bits width)
  ⟨s, hp, eq_mask_of_bitsAre hb⟩

theorem width_bits_le (width : Fin 4) : 8 * 2 ^ width.val ≤ 64 := by
  revert width
  exact fin4_cases (by decide) (by decide) (by decide) (by decide)

theorem reverseByteIndex_involutive (width : Fin 4) {i : Nat}
    (hi : i < 8 * 2 ^ width.val) :
    reverseByteIndex (8 * 2 ^ width.val) i < 8 * 2 ^ width.val ∧
      reverseByteIndex (8 * 2 ^ width.val)
        (reverseByteIndex (8 * 2 ^ width.val) i) = i := by
  unfold reverseByteIndex
  have hm : 0 < 2 ^ width.val := Nat.two_pow_pos width.val
  generalize 2 ^ width.val = m at hi hm ⊢
  constructor <;> omega

/-- Two byte reversals within one width recover the masked input. -/
theorem reverse_involutive (width : Fin 4) {x y z : Word}
    (h1 : ByteReversal (8 * 2 ^ width.val) x y)
    (h2 : ByteReversal (8 * 2 ^ width.val) y z) :
    z = x &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [h2 i hi, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hb : i < 8 * 2 ^ width.val
  · have ⟨hr, hrr⟩ := reverseByteIndex_involutive width hb
    have hr64 := Nat.lt_of_lt_of_le hr (width_bits_le width)
    rw [ite_prop_true hb, h1 _ hr64, ite_prop_true hr, hrr]
    simp only [hi, hb, decide_true, Bool.and_true]
  · rw [ite_prop_false hb]
    simp only [hb, decide_false, Bool.and_false]

end ProductionEndpoints

end
