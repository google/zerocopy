-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Side-Condition Reflection vs. Elaborator Tactics (`omega` / `decide`)

This module implements the `Trusted` side-condition specifications and `Theory`
pre-proved reflection checkers for 64-bit interval disjointness, power-of-two
alignment round-up, and symbolic-base subrange obligations.
-/

namespace Trusted

/-- 64-bit address space bound `2^64`. -/
def ADDR_LIMIT : Nat := 18446744073709551616

/-- 64-bit maximum address `2^64 - 1`. -/
def ADDR_MASK : Nat := 18446744073709551615

/-- Obligation Type 1: Two byte intervals `[p1, p1 + n1)` and `[p2, p2 + n2)`
    are disjoint and both fit within the 64-bit address space without wrapping. -/
def IntervalsDisjoint (p1 n1 p2 n2 : Nat) : Prop :=
  (p1 + n1 ≤ p2 ∨ p2 + n2 ≤ p1) ∧ p1 + n1 ≤ ADDR_MASK ∧ p2 + n2 ≤ ADDR_MASK

/-- Obligation Type 2: `out` is the aligned round-up of byte offset `off` to
    alignment `align`, is a multiple of `align`, and satisfies `off ≤ out < off + align`. -/
def AlignedRoundUp (off align out : Nat) : Prop :=
  out % align = 0 ∧ off ≤ out ∧ out < off + align

/-- Obligation Type 3: Universal symbolic pointer-offset subrange safety:
    for any base address `base : Nat`, `[base + off, base + off + sublen)` lies
    within `[base, base + totallen)`. -/
def SymbolicSubrange (off sublen totallen : Nat) : Prop :=
  ∀ (base : Nat), base + off + sublen ≤ base + totallen ∧ base ≤ base + off

end Trusted

namespace Theory

open Trusted

/-- Native GMP boolean checker for `IntervalsDisjoint`. Uses exclusively
    `Nat.add` and `Nat.ble`, which reduce in C++ via `type_checker::reduce_nat`. -/
def checkIntervalDisjoint (p1 n1 p2 n2 : Nat) : Bool :=
  (Nat.ble (p1 + n1) p2 || Nat.ble (p2 + n2) p1) &&
    Nat.ble (p1 + n1) ADDR_MASK &&
    Nat.ble (p2 + n2) ADDR_MASK

theorem checkIntervalDisjoint_sound {p1 n1 p2 n2 : Nat}
    (h : checkIntervalDisjoint p1 n1 p2 n2 = true) :
    IntervalsDisjoint p1 n1 p2 n2 := by
  unfold checkIntervalDisjoint at h
  unfold IntervalsDisjoint
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
  rcases h with ⟨⟨h1 | h2, h3⟩, h4⟩
  · exact ⟨Or.inl h1, h3, h4⟩
  · exact ⟨Or.inr h2, h3, h4⟩

/-- Native GMP boolean checker for `AlignedRoundUp`. Uses `Nat.mod`, `Nat.beq`,
    `Nat.add`, and `Nat.ble`, which reduce in C++ via `type_checker::reduce_nat`. -/
def checkAlignedRoundUp (off align out : Nat) : Bool :=
  Nat.beq (out % align) 0 &&
    Nat.ble off out &&
    Nat.ble (out + 1) (off + align)

theorem checkAlignedRoundUp_sound {off align out : Nat}
    (h : checkAlignedRoundUp off align out = true) :
    AlignedRoundUp off align out := by
  unfold checkAlignedRoundUp at h
  unfold AlignedRoundUp
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  rcases h with ⟨⟨hMod, hLe⟩, hLt⟩
  exact ⟨hMod, hLe, hLt⟩

/-- Native GMP boolean checker for `SymbolicSubrange`. Cancels the symbolic
    `base : Nat` quantifier once in `Theory` so per-crate proofs in `Proof.lean`
    only check `Nat.ble (off + sublen) totallen = true` by `rfl`! -/
def checkSymbolicSubrange (off sublen totallen : Nat) : Bool :=
  Nat.ble (off + sublen) totallen

theorem checkSymbolicSubrange_sound {off sublen totallen : Nat}
    (h : checkSymbolicSubrange off sublen totallen = true) :
    SymbolicSubrange off sublen totallen := by
  unfold checkSymbolicSubrange at h
  unfold SymbolicSubrange
  rw [Nat.ble_eq] at h
  intro base
  omega

/-- Bundled batch reflection for a list of `(p1, n1, p2, n2)` disjointness
    obligations, discharging all of them in a single `rfl` reduction. -/
def checkIntervalBatch : List (Nat × Nat × Nat × Nat) → Bool
  | [] => true
  | (p1, n1, p2, n2) :: rest =>
    checkIntervalDisjoint p1 n1 p2 n2 && checkIntervalBatch rest

def AllIntervalsDisjoint : List (Nat × Nat × Nat × Nat) → Prop
  | [] => True
  | (p1, n1, p2, n2) :: rest =>
    IntervalsDisjoint p1 n1 p2 n2 ∧ AllIntervalsDisjoint rest

theorem checkIntervalBatch_sound {xs : List (Nat × Nat × Nat × Nat)}
    (h : checkIntervalBatch xs = true) :
    AllIntervalsDisjoint xs := by
  induction xs with
  | nil => exact trivial
  | cons x rest ih =>
    rcases x with ⟨p1, n1, p2, n2⟩
    dsimp [checkIntervalBatch] at h
    rw [Bool.and_eq_true] at h
    exact ⟨checkIntervalDisjoint_sound h.1, ih h.2⟩

end Theory
