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
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Anneal.AiPcc.BitArith

public section

namespace Anneal.AiPcc

/-!
# Initialization and Tristate-Number Domains (`Anneal.AiPcc.Tnum`)

Constructive Pass-1 `InitDom` (initialized vs. maybe-uninitialized register
tracking) and `Tnum` (tristate known-value / unknown-mask domain) with sound
bitwise (`bitwiseAnd`, `bitwiseOr`, `bitwiseXor`, `shl`, `shr`), modular
arithmetic (`add`, `neg`, `sub`), and lattice (`join`, `meet`) operations.

Unlike `Anneal.BitVec` (which operates over width-indexed `BitVec w`), `Tnum`
represents abstract bitvectors as width-erased `(val, mask : Nat)` pairs so a
single `MirAbsEnv` can analyze heterogeneous MIR local widths (`u8`..`u128`,
`usize`) without dependent type casts.
-/

/-! ### `InitDom` (Register Initialization Domain) -/

/-- Initialization lattice: `.bot` (unreachable), `.init` (definitely
initialized), and `.uninit` (possibly uninitialized top). -/
inductive InitDom where
  | bot
  | init
  | uninit

/-- Partial order `.bot ⊑ .init ⊑ .uninit` on `InitDom`. -/
@[expose] def InitDom.le (a b : InitDom) : Bool :=
  match a, b with
  | .bot, _ => true
  | .init, .init => true
  | .init, .uninit => true
  | .uninit, .uninit => true
  | _, _ => false

/-- Least upper bound on `InitDom`. -/
@[expose] def InitDom.join (a b : InitDom) : InitDom :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | .init, .init => .init
  | _, _ => .uninit

/-- Greatest lower bound on `InitDom`. -/
@[expose] def InitDom.meet (a b : InitDom) : InitDom :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .uninit, x => x
  | x, .uninit => x
  | .init, .init => .init

/-- Concretization of `InitDom` against an `Option Nat` slot in `[0, M)`
(`.uninit` admits both `none` and initialized `some x`). -/
@[expose] def InitDom.denote (M : Nat) (d : InitDom) (v : Option Nat) : Prop :=
  match d with
  | .bot => False
  | .init => ∃ x : Nat, v = some x ∧ x < M
  | .uninit => match v with | none => True | some x => x < M

/-- Soundness of `InitDom.le` with respect to `InitDom.denote`. -/
theorem initDom_le_sound (M : Nat) {a b : InitDom} {v : Option Nat}
    (hLe : InitDom.le a b = true) (ha : InitDom.denote M a v) : InitDom.denote M b v := by
  cases a with
  | bot => exact False.elim ha
  | init =>
    cases b with
    | bot => nomatch hLe
    | init => exact ha
    | uninit =>
      dsimp only [InitDom.denote] at ha; dsimp only [InitDom.denote]
      cases ha with | intro x hx => rw [hx.1]; exact hx.2
  | uninit =>
    cases b with
    | bot => nomatch hLe
    | init => nomatch hLe
    | uninit => exact ha

/-! ### `Tnum` (Tristate Numbers with Constructive Bitwise Soundness) -/

/-- Tristate number `(val, mask)`: bits `0` in `mask` have known value `val`;
bits `1` in `mask` are unknown (with `val &&& mask = 0`). -/
structure Tnum where
  val  : Nat
  mask : Nat

/-- Well-formedness invariant `val &&& mask == 0` (unknown bits carry `0` in
`val`). -/
@[expose] def Tnum.wf (t : Tnum) : Bool :=
  Nat.beq (Nat.land t.val t.mask) 0

/-- Concretization of `t : Tnum`: `t` is well-formed and `x` agrees with `t.val`
on all known bits (`x ||| t.mask = t.val ||| t.mask`). -/
@[expose] def Tnum.denote (t : Tnum) (x : Nat) : Prop :=
  t.wf = true ∧ Nat.lor x t.mask = Nat.lor t.val t.mask

/-- Bitwise characterization of `Tnum.denote`. -/
theorem tnum_denote_iff_bitAt (t : Tnum) (x : Nat) :
    t.denote x ↔ (t.wf = true ∧ ∀ k : Nat, bitAt t.mask k = false → bitAt x k = bitAt t.val k) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro k hm0
    have hBit : bitAt (Nat.lor x t.mask) k = bitAt (Nat.lor t.val t.mask) k := by rw [h.2]
    rw [bitAt_lor, bitAt_lor, hm0, Bool.or_false, Bool.or_false] at hBit
    exact hBit
  · intro h
    refine ⟨h.1, ?_⟩
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_lor, bitAt_lor]
    cases hm : bitAt t.mask k with
    | true => rw [Bool.or_true, Bool.or_true]
    | false => rw [h.2 k hm]

/-- Exact `w`-bit tristate constant `⟨wrapVal w c, 0⟩`. -/
@[expose] def Tnum.const (w c : Nat) : Tnum :=
  ⟨wrapVal w c, 0⟩

/-- Top `w`-bit tristate number `⟨0, 2^w - 1⟩` (all `w` bits unknown). -/
@[expose] def Tnum.top (w : Nat) : Tnum :=
  ⟨0, modPow2 w - 1⟩

/-- Decidable inclusion check `a ⊑ b` on `Tnum`. -/
@[expose] def Tnum.le (a b : Tnum) : Bool :=
  b.wf &&
    Nat.beq (Nat.lor a.mask b.mask) b.mask &&
    Nat.beq (Nat.lor a.val b.mask) (Nat.lor b.val b.mask)

/-- Least upper bound `a ⊔ b` on `Tnum`. -/
@[expose] def Tnum.join (a b : Tnum) : Tnum :=
  let diff := Nat.xor a.val b.val
  let mu := Nat.lor diff (Nat.lor a.mask b.mask)
  let v := andNot (Nat.land a.val b.val) mu
  ⟨v, mu⟩

/-- Partial meet `a ⊓ b` on `Tnum` (`none` when known bits conflict). -/
@[expose] def Tnum.meet (a b : Tnum) : Option Tnum :=
  let mu := Nat.lor a.mask b.mask
  match Nat.beq (Nat.lor a.val mu) (Nat.lor b.val mu) with
  | false => none
  | true =>
    let nm := Nat.land a.mask b.mask
    let nv := andNot (Nat.lor a.val b.val) nm
    some ⟨nv, nm⟩

/-- Abstract bitwise AND transfer on `Tnum`. -/
@[expose] def Tnum.bitwiseAnd (a b : Tnum) : Tnum :=
  let v := Nat.land a.val b.val
  let m := Nat.lor (Nat.land a.mask b.mask)
             (Nat.lor (Nat.land a.mask b.val) (Nat.land b.mask a.val))
  ⟨andNot v m, m⟩

/-- Abstract bitwise OR transfer on `Tnum`. -/
@[expose] def Tnum.bitwiseOr (a b : Tnum) : Tnum :=
  let v := Nat.lor a.val b.val
  let m := andNot (Nat.lor a.mask b.mask) v
  ⟨v, m⟩

/-- Abstract bitwise XOR transfer on `Tnum`. -/
@[expose] def Tnum.bitwiseXor (a b : Tnum) : Tnum :=
  let m := Nat.lor a.mask b.mask
  ⟨andNot (Nat.xor a.val b.val) m, m⟩

/-- Abstract `w`-bit logical left shift by `s` bits on `Tnum`. -/
@[expose] def Tnum.shl (w s : Nat) (a : Tnum) : Tnum :=
  match Nat.ble s w && Nat.ble s 128 with
  | false => Tnum.top w
  | true =>
    ⟨wrapVal w (Nat.shiftLeft a.val s), wrapVal w (Nat.shiftLeft a.mask s)⟩

/-- Abstract logical right shift by `s` bits on `Tnum`. -/
@[expose] def Tnum.shr (s : Nat) (a : Tnum) : Tnum :=
  ⟨Nat.shiftRight a.val s, Nat.shiftRight a.mask s⟩

/-- Carry-propagating `w`-bit modular addition transfer on `Tnum`. -/
@[expose] def Tnum.add (w : Nat) (a b : Tnum) : Tnum :=
  let sm := a.mask + b.mask
  let sv := a.val + b.val
  let sigma := sm + sv
  let chi := Nat.xor sigma sv
  let mu := wrapVal w (Nat.lor chi (Nat.lor a.mask b.mask))
  let rv := wrapVal w (andNot sv mu)
  ⟨rv, mu⟩

/-- Abstract `w`-bit two's-complement negation on `Tnum`. -/
@[expose] def Tnum.neg (w : Nat) (a : Tnum) : Tnum :=
  let allOnes := modPow2 w - 1
  let flipped := andNot (Nat.xor a.val allOnes) a.mask
  Tnum.add w ⟨wrapVal w flipped, wrapVal w a.mask⟩ (Tnum.const w 1)

/-- Abstract `w`-bit modular subtraction `a + (-b)` on `Tnum`. -/
@[expose] def Tnum.sub (w : Nat) (a b : Tnum) : Tnum :=
  Tnum.add w a (Tnum.neg w b)

/-- Clears known/unknown bits at index `≥ k` when `x < 2^k`. -/
@[expose] def Tnum.capPow2 (k : Nat) (a : Tnum) : Tnum :=
  let msk := modPow2 k - 1
  ⟨Nat.land a.val msk, Nat.land a.mask msk⟩

/-- `⟨andNot v m, m⟩` always satisfies `Tnum.wf`. -/
theorem tnum_wf_andNot (v m : Nat) : (Tnum.mk (andNot v m) m).wf = true := by
  dsimp only [Tnum.wf]
  apply nat_beq_of_eq
  apply nat_eq_of_bitAt
  intro k
  rw [bitAt_land, bitAt_andNot, bitAt_zero_nat]
  cases bitAt v k <;> cases bitAt m k <;> rfl

/-- Soundness of `Tnum.const w x` when `x < 2^w`. -/
theorem tnum_const_sound {w x : Nat} (hLt : x < modPow2 w) :
    (Tnum.const w x).denote x := by
  rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.const, Tnum.wf, wrapVal]
  refine ⟨?_, ?_⟩
  · have hZero : Nat.land (Nat.mod x (modPow2 w)) 0 = 0 := by
      apply nat_eq_of_bitAt; intro k; rw [bitAt_land, bitAt_zero_nat, Bool.and_false]
    rw [hZero]; rfl
  · intro k _
    have hMod : Nat.mod x (modPow2 w) = x := Nat.mod_eq_of_lt hLt
    rw [hMod]

/-- Soundness of `Tnum.const w c` on `wrapVal w c`. -/
theorem tnum_const_wrap_sound {w c : Nat} :
    (Tnum.const w c).denote (wrapVal w c) := by
  have hLt : wrapVal w c < modPow2 w := Nat.mod_lt c (modPow2_pos w)
  have h := tnum_const_sound hLt
  dsimp only [Tnum.const, wrapVal] at h; dsimp only [Tnum.const, wrapVal]
  have hm : Nat.mod (Nat.mod c (modPow2 w)) (modPow2 w) = Nat.mod c (modPow2 w) :=
    Nat.mod_eq_of_lt (Nat.mod_lt c (modPow2_pos w))
  rw [hm] at h
  exact h

/-- Bit `k` of `2^w - 1` equals `k < w`. -/
theorem bitAt_modPow2_sub_one : ∀ w k : Nat, bitAt (modPow2 w - 1) k = Nat.blt k w
  | 0, k => by rw [modPow2_zero, Nat.sub_self, bitAt_zero_nat]; rfl
  | w + 1, 0 => by
    have hPos : 1 ≤ modPow2 w := modPow2_pos w
    have hEq : modPow2 (w + 1) - 1 = 2 * (modPow2 w - 1) + 1 := by
      rw [modPow2_succ w]
      have hw : modPow2 w = (modPow2 w - 1) + 1 := (Nat.sub_add_cancel hPos).symm
      rw [hw, Nat.mul_add 2 (modPow2 w - 1) 1, Nat.mul_one]
      rfl
    rw [hEq, bitAt_zero, mod2_two_mul_add_one]
    rfl
  | w + 1, k + 1 => by
    have hPos : 1 ≤ modPow2 w := modPow2_pos w
    have hEq : modPow2 (w + 1) - 1 = 2 * (modPow2 w - 1) + 1 := by
      rw [modPow2_succ w]
      have hw : modPow2 w = (modPow2 w - 1) + 1 := (Nat.sub_add_cancel hPos).symm
      rw [hw, Nat.mul_add 2 (modPow2 w - 1) 1, Nat.mul_one]
      rfl
    rw [hEq, bitAt_succ, div2_two_mul_add_one, bitAt_modPow2_sub_one w k]
    cases hk : Nat.blt k w with
    | true =>
      exact (blt_true_of_lt (Nat.succ_lt_succ (lt_of_blt_true hk))).symm
    | false =>
      have hNot : ¬ (k < w) := fun h => by
        have ht := blt_true_of_lt h; rw [ht] at hk; nomatch hk
      cases hS : Nat.blt (k + 1) (w + 1) with
      | false => rfl
      | true => exact False.elim (hNot (Nat.lt_of_succ_lt_succ (lt_of_blt_true hS)))

/-- `Tnum.top w` denotes every `x < 2^w`. -/
theorem tnum_top_sound {w x : Nat} (hxLt : x < modPow2 w) : (Tnum.top w).denote x := by
  rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.top, Tnum.wf]
  refine ⟨?_, ?_⟩
  · have hZero : Nat.land 0 (modPow2 w - 1) = 0 := by
      apply nat_eq_of_bitAt; intro k; rw [bitAt_land, bitAt_zero_nat, Bool.false_and]
    rw [hZero]; rfl
  · intro k hk
    rw [bitAt_modPow2_sub_one] at hk
    have hNot : ¬ (k < w) := fun h => by
      have ht := blt_true_of_lt h; rw [ht] at hk; nomatch hk
    rw [bitAt_zero_nat, bitAt_zero_ge_of_lt_modPow2 hxLt k (Nat.le_of_not_lt hNot)]

/-- Soundness of `Tnum.le`. -/
theorem tnum_le_sound {a b : Tnum} {x : Nat}
    (hLe : Tnum.le a b = true) (ha : a.denote x) : b.denote x := by
  dsimp only [Tnum.le] at hLe
  have h12 := bool_and_true_left hLe
  have hbw := bool_and_true_left h12
  have hMask := bool_and_true_right h12
  have hVal := bool_and_true_right hLe
  have hMEq : Nat.lor a.mask b.mask = b.mask := Nat.eq_of_beq_eq_true hMask
  have hVEq : Nat.lor a.val b.mask = Nat.lor b.val b.mask := Nat.eq_of_beq_eq_true hVal
  rw [tnum_denote_iff_bitAt] at ha; rw [tnum_denote_iff_bitAt]
  refine ⟨hbw, ?_⟩
  intro k hbm0
  have hm : bitAt (Nat.lor a.mask b.mask) k = bitAt b.mask k := by rw [hMEq]
  rw [bitAt_lor, hbm0, Bool.or_false] at hm
  have hv : bitAt (Nat.lor a.val b.mask) k = bitAt (Nat.lor b.val b.mask) k := by rw [hVEq]
  rw [bitAt_lor, bitAt_lor, hbm0, Bool.or_false, Bool.or_false] at hv
  rw [ha.2 k hm, hv]

/-- Interval bounds implied by `t.denote x`: `t.val ≤ x ≤ t.val + t.mask`. -/
theorem tnum_bounds {t : Tnum} {x : Nat} (h : t.denote x) :
    t.val ≤ x ∧ x ≤ t.val + t.mask := by
  rw [tnum_denote_iff_bitAt] at h
  have hWf : Nat.land t.val t.mask = 0 := Nat.eq_of_beq_eq_true h.1
  let u := Nat.land x t.mask
  have hDisj : Nat.land t.val u = 0 := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_land, bitAt_land, bitAt_zero_nat]
    have hWfk : bitAt (Nat.land t.val t.mask) k = bitAt 0 k := by rw [hWf]
    rw [bitAt_land, bitAt_zero_nat] at hWfk
    cases hav : bitAt t.val k with
    | false => rfl
    | true =>
      cases ham : bitAt t.mask k with
      | false => rw [Bool.and_false, Bool.and_false]
      | true => rw [hav, ham] at hWfk; nomatch hWfk
  have hSum : Nat.lor t.val u = x := by
    apply nat_eq_of_bitAt
    intro k
    rw [bitAt_lor, bitAt_land]
    cases hm : bitAt t.mask k with
    | false => rw [Bool.and_false, Bool.or_false]; exact (h.2 k hm).symm
    | true =>
      have hWfk : bitAt (Nat.land t.val t.mask) k = bitAt 0 k := by rw [hWf]
      rw [bitAt_land, bitAt_zero_nat, hm, Bool.and_true] at hWfk
      rw [hWfk, Bool.and_true, Bool.false_or]
  have hEq : x = t.val + u := by
    rw [nat_add_eq_lor_of_disjoint t.val u hDisj, hSum]
  have huLe : u ≤ t.mask := by
    apply nat_le_of_bitAt_imp
    intro k hk
    dsimp only [u] at hk
    rw [bitAt_land] at hk
    exact bool_and_true_right hk
  rw [hEq]
  exact ⟨Nat.le_add_right t.val u, Nat.add_le_add_left huLe t.val⟩

/-- Left upper-bound soundness of `Tnum.join`. -/
theorem tnum_join_sound_left {a b : Tnum} {x : Nat} (ha : a.denote x) :
    (Tnum.join a b).denote x := by
  rw [tnum_denote_iff_bitAt] at ha; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.join]
  refine ⟨tnum_wf_andNot _ _, ?_⟩
  intro k hm0
  rw [bitAt_andNot, bitAt_land, hm0, Bool.not_false, Bool.and_true]
  rw [bitAt_lor, bitAt_lor, bitAt_xor] at hm0
  have hd := bool_or_false_left hm0
  have hMasks := bool_or_false_right hm0
  have haM := bool_or_false_left hMasks
  rw [ha.2 k haM]
  cases hav : bitAt a.val k <;> cases hbv : bitAt b.val k <;>
    first | rfl | (rw [hav, hbv] at hd; nomatch hd)

/-- Right upper-bound soundness of `Tnum.join`. -/
theorem tnum_join_sound_right {a b : Tnum} {x : Nat} (hb : b.denote x) :
    (Tnum.join a b).denote x := by
  rw [tnum_denote_iff_bitAt] at hb; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.join]
  refine ⟨tnum_wf_andNot _ _, ?_⟩
  intro k hm0
  rw [bitAt_andNot, bitAt_land, hm0, Bool.not_false, Bool.and_true]
  rw [bitAt_lor, bitAt_lor, bitAt_xor] at hm0
  have hd := bool_or_false_left hm0
  have hMasks := bool_or_false_right hm0
  have hbM := bool_or_false_right hMasks
  rw [hb.2 k hbM]
  cases hav : bitAt a.val k <;> cases hbv : bitAt b.val k <;>
    first | rfl | (rw [hav, hbv] at hd; nomatch hd)

/-- Soundness of `Tnum.meet` when it returns `some res`. -/
theorem tnum_meet_sound {a b res : Tnum} {x : Nat}
    (ha : a.denote x) (hb : b.denote x) (hRes : Tnum.meet a b = some res) :
    res.denote x := by
  dsimp only [Tnum.meet] at hRes
  cases hCompat : Nat.beq (Nat.lor a.val (Nat.lor a.mask b.mask))
                          (Nat.lor b.val (Nat.lor a.mask b.mask)) with
  | false => rw [hCompat] at hRes; nomatch hRes
  | true =>
    rw [hCompat] at hRes
    injection hRes with hEq
    rw [← hEq, tnum_denote_iff_bitAt]
    rw [tnum_denote_iff_bitAt] at ha hb
    refine ⟨tnum_wf_andNot _ _, ?_⟩
    intro k hm0
    rw [bitAt_land] at hm0
    rw [bitAt_andNot, bitAt_lor, bitAt_land, hm0, Bool.not_false, Bool.and_true]
    cases haM : bitAt a.mask k <;> cases hbM : bitAt b.mask k
    · have hvEq : bitAt a.val k = bitAt b.val k := by rw [← ha.2 k haM, hb.2 k hbM]
      rw [ha.2 k haM, hvEq]; cases bitAt b.val k <;> rfl
    · have hWfB : Nat.land b.val b.mask = 0 := Nat.eq_of_beq_eq_true hb.1
      have hZeroB : bitAt (Nat.land b.val b.mask) k = bitAt 0 k := by rw [hWfB]
      rw [bitAt_land, bitAt_zero_nat, hbM, Bool.and_true] at hZeroB
      rw [ha.2 k haM, hZeroB]; cases bitAt a.val k <;> rfl
    · have hWfA : Nat.land a.val a.mask = 0 := Nat.eq_of_beq_eq_true ha.1
      have hZeroA : bitAt (Nat.land a.val a.mask) k = bitAt 0 k := by rw [hWfA]
      rw [bitAt_land, bitAt_zero_nat, haM, Bool.and_true] at hZeroA
      rw [hb.2 k hbM, hZeroA]; cases bitAt b.val k <;> rfl
    · rw [haM, hbM] at hm0; nomatch hm0

/-- If `x` satisfies both `a` and `b`, then `Tnum.meet a b ≠ none`. -/
theorem tnum_meet_none_impossible {a b : Tnum} {x : Nat}
    (ha : a.denote x) (hb : b.denote x) : Tnum.meet a b ≠ none := by
  intro hNone
  dsimp only [Tnum.meet] at hNone
  cases hCompat : Nat.beq (Nat.lor a.val (Nat.lor a.mask b.mask))
                          (Nat.lor b.val (Nat.lor a.mask b.mask)) with
  | true => rw [hCompat] at hNone; nomatch hNone
  | false =>
    have hEq : Nat.lor a.val (Nat.lor a.mask b.mask) =
               Nat.lor b.val (Nat.lor a.mask b.mask) := by
      apply nat_eq_of_bitAt
      intro k
      rw [bitAt_lor, bitAt_lor, bitAt_lor, bitAt_lor]
      rw [tnum_denote_iff_bitAt] at ha hb
      cases hmA : bitAt a.mask k <;> cases hmB : bitAt b.mask k
      · rw [← ha.2 k hmA, ← hb.2 k hmB]
      · rw [Bool.or_true, Bool.or_true, Bool.or_true]
      · rw [Bool.true_or, Bool.or_true, Bool.or_true]
      · rw [Bool.or_true, Bool.or_true, Bool.or_true]
    rw [nat_beq_of_eq hEq] at hCompat
    nomatch hCompat

/-- Soundness of `Tnum.bitwiseAnd` over `Nat.land`. -/
theorem tnum_bitwiseAnd_sound {a b : Tnum} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) : (Tnum.bitwiseAnd a b).denote (Nat.land x y) := by
  rw [tnum_denote_iff_bitAt] at ha hb; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.bitwiseAnd]
  refine ⟨tnum_wf_andNot _ _, ?_⟩
  intro k hm0
  rw [bitAt_land, bitAt_andNot, bitAt_land, hm0, Bool.not_false, Bool.and_true]
  rw [bitAt_lor, bitAt_land, bitAt_lor, bitAt_land, bitAt_land] at hm0
  have hM1 := bool_or_false_left hm0
  have hM23 := bool_or_false_right hm0
  have hM2 := bool_or_false_left hM23
  have hM3 := bool_or_false_right hM23
  cases ham : bitAt a.mask k with
  | false =>
    cases hbm : bitAt b.mask k with
    | false => rw [ha.2 k ham, hb.2 k hbm]
    | true =>
      rw [hbm, Bool.true_and] at hM3
      rw [ha.2 k ham, hM3, Bool.false_and, Bool.false_and]
  | true =>
    cases hbm : bitAt b.mask k with
    | true => rw [ham, hbm] at hM1; nomatch hM1
    | false =>
      rw [ham, Bool.true_and] at hM2
      rw [hb.2 k hbm, hM2, Bool.and_false, Bool.and_false]

/-- Soundness of `Tnum.bitwiseOr` over `Nat.lor`. -/
theorem tnum_bitwiseOr_sound {a b : Tnum} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) : (Tnum.bitwiseOr a b).denote (Nat.lor x y) := by
  rw [tnum_denote_iff_bitAt] at ha hb; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.bitwiseOr]
  refine ⟨?_, ?_⟩
  · dsimp only [Tnum.wf]
    apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro k
    rw [bitAt_land, bitAt_andNot, bitAt_zero_nat]
    cases bitAt (Nat.lor a.val b.val) k <;> cases bitAt (Nat.lor a.mask b.mask) k <;> rfl
  · intro k hm0
    rw [bitAt_andNot, bitAt_lor, bitAt_lor] at hm0
    rw [bitAt_lor, bitAt_lor]
    cases hv : bitAt a.val k || bitAt b.val k with
    | true =>
      cases hav : bitAt a.val k <;> cases hbv : bitAt b.val k
      · rw [hav, hbv] at hv; nomatch hv
      · have hbm : bitAt b.mask k = false := by
          have hb0 : bitAt (Nat.land b.val b.mask) k = bitAt 0 k := by
            rw [Nat.eq_of_beq_eq_true hb.1]
          rw [bitAt_land, bitAt_zero_nat, hbv, Bool.true_and] at hb0; exact hb0
        rw [hb.2 k hbm, hbv, Bool.or_true]
      · have ham : bitAt a.mask k = false := by
          have ha0 : bitAt (Nat.land a.val a.mask) k = bitAt 0 k := by
            rw [Nat.eq_of_beq_eq_true ha.1]
          rw [bitAt_land, bitAt_zero_nat, hav, Bool.true_and] at ha0; exact ha0
        rw [ha.2 k ham, hav, Bool.true_or]
      · have ham : bitAt a.mask k = false := by
          have ha0 : bitAt (Nat.land a.val a.mask) k = bitAt 0 k := by
            rw [Nat.eq_of_beq_eq_true ha.1]
          rw [bitAt_land, bitAt_zero_nat, hav, Bool.true_and] at ha0; exact ha0
        rw [ha.2 k ham, hav, Bool.true_or]
    | false =>
      rw [hv, Bool.not_false, Bool.and_true] at hm0
      have ham := bool_or_false_left hm0
      have hbm := bool_or_false_right hm0
      rw [ha.2 k ham, hb.2 k hbm, hv]

/-- Soundness of `Tnum.bitwiseXor` over `Nat.xor`. -/
theorem tnum_bitwiseXor_sound {a b : Tnum} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) : (Tnum.bitwiseXor a b).denote (Nat.xor x y) := by
  rw [tnum_denote_iff_bitAt] at ha hb; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.bitwiseXor]
  refine ⟨tnum_wf_andNot _ _, ?_⟩
  intro k hm0
  rw [bitAt_xor, bitAt_andNot, bitAt_xor, hm0, Bool.not_false, Bool.and_true]
  rw [bitAt_lor] at hm0
  rw [ha.2 k (bool_or_false_left hm0), hb.2 k (bool_or_false_right hm0)]

/-- Soundness of `Tnum.shl` over `w`-bit `Nat.shiftLeft`. -/
theorem tnum_shl_sound {w s : Nat} {a : Tnum} {x : Nat}
    (ha : a.denote x) :
    (Tnum.shl w s a).denote (wrapVal w (Nat.shiftLeft x s)) := by
  dsimp only [Tnum.shl]
  cases hCond : Nat.ble s w && Nat.ble s 128 with
  | false => exact tnum_top_sound (Nat.mod_lt _ (modPow2_pos w))
  | true =>
    rw [tnum_denote_iff_bitAt] at ha; rw [tnum_denote_iff_bitAt]
    dsimp only [Tnum.wf, wrapVal]
    refine ⟨?_, ?_⟩
    · apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro k
      rw [bitAt_land, bitAt_mod_modPow2, bitAt_mod_modPow2, bitAt_zero_nat]
      cases Nat.blt k w with
      | false => rfl
      | true =>
        rw [bitAt_shiftLeft, bitAt_shiftLeft]
        cases Nat.ble s k with
        | false => rfl
        | true =>
          have hWfA : bitAt (Nat.land a.val a.mask) (k - s) = bitAt 0 (k - s) := by
            rw [Nat.eq_of_beq_eq_true ha.1]
          rw [bitAt_land, bitAt_zero_nat] at hWfA
          exact hWfA
    · intro k hm0
      rw [bitAt_mod_modPow2] at hm0
      rw [bitAt_mod_modPow2, bitAt_mod_modPow2]
      cases hkw : Nat.blt k w with
      | false => rfl
      | true =>
        rw [hkw] at hm0
        rw [bitAt_shiftLeft] at hm0
        rw [bitAt_shiftLeft, bitAt_shiftLeft]
        cases hsk : Nat.ble s k with
        | false => rfl
        | true =>
          rw [hsk] at hm0
          exact ha.2 (k - s) hm0

/-- Soundness of `Tnum.shr` over `Nat.shiftRight`. -/
theorem tnum_shr_sound {s : Nat} {a : Tnum} {x : Nat}
    (ha : a.denote x) : (Tnum.shr s a).denote (Nat.shiftRight x s) := by
  rw [tnum_denote_iff_bitAt] at ha; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.shr, Tnum.wf]
  refine ⟨?_, ?_⟩
  · apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro k
    rw [bitAt_land, bitAt_shiftRight, bitAt_shiftRight, bitAt_zero_nat]
    have hWfA : bitAt (Nat.land a.val a.mask) (k + s) = bitAt 0 (k + s) := by
      rw [Nat.eq_of_beq_eq_true ha.1]
    rw [bitAt_land, bitAt_zero_nat] at hWfA
    exact hWfA
  · intro k hm0
    rw [bitAt_shiftRight] at hm0
    rw [bitAt_shiftRight, bitAt_shiftRight]
    exact ha.2 (k + s) hm0

/-- Soundness of `Tnum.capPow2 k a` when `x < 2^k`. -/
theorem tnum_capPow2_sound {k : Nat} {a : Tnum} {x : Nat}
    (ha : a.denote x) (hxLt : x < modPow2 k) :
    (Tnum.capPow2 k a).denote x := by
  rw [tnum_denote_iff_bitAt] at ha; rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.capPow2, Tnum.wf]
  refine ⟨?_, ?_⟩
  · apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro j
    rw [bitAt_land, bitAt_land, bitAt_land, bitAt_zero_nat]
    have hWfA : bitAt (Nat.land a.val a.mask) j = bitAt 0 j := by
      rw [Nat.eq_of_beq_eq_true ha.1]
    rw [bitAt_land, bitAt_zero_nat] at hWfA
    cases hav : bitAt a.val j with
    | false => cases hmk : bitAt (modPow2 k - 1) j <;> rfl
    | true =>
      cases ham : bitAt a.mask j with
      | false => cases hmk : bitAt (modPow2 k - 1) j <;> rfl
      | true => rw [hav, ham] at hWfA; nomatch hWfA
  · intro j hm0
    rw [bitAt_land, bitAt_modPow2_sub_one] at hm0
    rw [bitAt_land, bitAt_modPow2_sub_one]
    cases hjk : Nat.blt j k with
    | true =>
      rw [hjk, Bool.and_true] at hm0
      rw [Bool.and_true]
      exact ha.2 j hm0
    | false =>
      have hNot : ¬ (j < k) := fun hLt => by
        have ht := blt_true_of_lt hLt; rw [ht] at hjk; nomatch hjk
      rw [Bool.and_false]
      exact bitAt_zero_ge_of_lt_modPow2 hxLt j (Nat.le_of_not_lt hNot)

-- `Tnum.add` Constructive Prefix-Carry Soundness Helpers

/-- Prefix sum bound `(a mod 2^k) + (m mod 2^k) < 2^k` when `a &&& m = 0`. -/
theorem tnum_prefix_disjoint_lt {a m : Nat} (hDisj : Nat.land a m = 0) (k : Nat) :
    Nat.mod a (modPow2 k) + Nat.mod m (modPow2 k) < modPow2 k := by
  let P := modPow2 k
  have hDisjMod : Nat.land (Nat.mod a P) (Nat.mod m P) = 0 := by
    apply nat_eq_of_bitAt
    intro j
    rw [bitAt_land, bitAt_mod_modPow2, bitAt_mod_modPow2, bitAt_zero_nat]
    cases Nat.blt j k with
    | false => rfl
    | true =>
      have hWf : bitAt (Nat.land a m) j = bitAt 0 j := by rw [hDisj]
      rw [bitAt_land, bitAt_zero_nat] at hWf
      exact hWf
  have hEqLor := nat_add_eq_lor_of_disjoint (Nat.mod a P) (Nat.mod m P) hDisjMod
  rw [hEqLor]
  apply lt_modPow2_of_bitAt_zero
  intro j hj
  rw [bitAt_lor, bitAt_mod_modPow2, bitAt_mod_modPow2]
  have hNot : Nat.blt j k = false := by
    cases hb : Nat.blt j k with
    | false => rfl
    | true => exact False.elim (Nat.not_le_of_gt (lt_of_blt_true hb) hj)
  rw [hNot]; rfl

/-- If `bitAt m k = false`, then `m mod (2 * 2^k) = m mod 2^k`. -/
theorem bit_zero_mod_two_mul {m k : Nat} (h0 : bitAt m k = false) :
    Nat.mod m (2 * modPow2 k) = Nat.mod m (modPow2 k) := by
  apply nat_eq_of_bitAt
  intro j
  rw [← modPow2_succ k, bitAt_mod_modPow2, bitAt_mod_modPow2]
  cases hj : Nat.blt j k with
  | true =>
    have hS : Nat.blt j (k + 1) = true :=
      blt_true_of_lt (Nat.lt_trans (lt_of_blt_true hj) (Nat.lt_succ_self k))
    rw [hS]
  | false =>
    have hGe : k ≤ j := Nat.le_of_not_lt (fun hLt => by
      have ht := blt_true_of_lt hLt; rw [ht] at hj; nomatch hj)
    cases hEq : Nat.beq j k with
    | true =>
      have hJk : j = k := Nat.eq_of_beq_eq_true hEq
      rw [hJk]
      have hS : Nat.blt k (k + 1) = true := blt_true_of_lt (Nat.lt_succ_self k)
      rw [hS, h0]
    | false =>
      have hNe : j ≠ k := fun h => by rw [h, nat_beq_refl] at hEq; nomatch hEq
      have hGt : k + 1 ≤ j := Nat.lt_of_le_of_ne hGe hNe.symm
      have hS : Nat.blt j (k + 1) = false := by
        cases hb : Nat.blt j (k + 1) with
        | false => rfl
        | true => exact False.elim (Nat.not_le_of_gt (lt_of_blt_true hb) hGt)
      rw [hS]

/-- Decomposition of `m` at bit `k` when `bitAt m k = false`. -/
theorem nat_decomp_even_bit_zero {m k : Nat} (h0 : bitAt m k = false) :
    m = 2 * Nat.div m (2 * modPow2 k) * modPow2 k + Nat.mod m (modPow2 k) := by
  have hDiv := Nat.div_add_mod m (2 * modPow2 k)
  dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at hDiv
  rw [bit_zero_mod_two_mul h0] at hDiv
  have hAssoc : (2 * modPow2 k) * Nat.div m (2 * modPow2 k) =
      2 * Nat.div m (2 * modPow2 k) * modPow2 k := by
    rw [Nat.mul_assoc, Nat.mul_comm (modPow2 k) _, ← Nat.mul_assoc]
  rw [← hAssoc]
  exact hDiv.symm

/-- Adding an even multiple of `2^k` preserves bit `k` of a sum. -/
theorem nat_div_mod2_shift_even (sv q k dLo : Nat) :
    Nat.mod (Nat.div (sv + (2 * q * modPow2 k + dLo)) (modPow2 k)) 2 =
      Nat.mod (Nat.div sv (modPow2 k) + Nat.div (Nat.mod sv (modPow2 k) + dLo) (modPow2 k)) 2 := by
  let P := modPow2 k
  have hP : 0 < P := modPow2_pos k
  have hSv := Nat.div_add_mod sv P
  dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at hSv
  have hExpr : sv + (2 * q * P + dLo) = (Nat.mod sv P + dLo) + P * (Nat.div sv P + 2 * q) := by
    have h1 : (P * Nat.div sv P + Nat.mod sv P) + (2 * q * P + dLo) =
        (Nat.mod sv P + dLo) + P * (Nat.div sv P + 2 * q) := by
      rw [Nat.mul_add P (Nat.div sv P) (2 * q), Nat.mul_comm P (2 * q)]
      rw [Nat.add_assoc (P * Nat.div sv P) (Nat.mod sv P) (2 * q * P + dLo)]
      rw [← Nat.add_assoc (Nat.mod sv P) (2 * q * P) dLo, Nat.add_comm (Nat.mod sv P) (2 * q * P)]
      rw [Nat.add_assoc (2 * q * P) (Nat.mod sv P) dLo,
          ← Nat.add_assoc (P * Nat.div sv P) (2 * q * P)]
      rw [Nat.add_comm (P * Nat.div sv P + 2 * q * P) (Nat.mod sv P + dLo)]
    rw [hSv] at h1
    exact h1
  rw [hExpr]
  have hDiv := Nat.add_mul_div_left (Nat.mod sv P + dLo) (Nat.div sv P + 2 * q) hP
  dsimp only [HDiv.hDiv, Div.div] at hDiv
  rw [hDiv, ← Nat.add_assoc, Nat.add_comm (Nat.div (Nat.mod sv P + dLo) P) (Nat.div sv P)]
  exact Nat.add_mul_mod_self_left (Nat.div sv P + Nat.div (Nat.mod sv P + dLo) P) 2 q

/-- Core carry-free bit agreement lemma for Vishwanathan et al.'s `Tnum.add`. -/
theorem tnum_add_bit_helper {x y : Nat} {a b : Tnum}
    (ha : a.denote x) (hb : b.denote y) (k : Nat)
    (hMu0 : bitAt (Nat.lor (Nat.xor (a.mask + b.mask + (a.val + b.val)) (a.val + b.val))
                     (Nat.lor a.mask b.mask)) k = false) :
    bitAt (x + y) k = bitAt (a.val + b.val) k := by
  let P := modPow2 k
  have hP : 0 < P := modPow2_pos k
  rw [bitAt_lor, bitAt_lor, bitAt_xor] at hMu0
  have hXor0 := bool_or_false_left hMu0
  have hMasks0 := bool_or_false_right hMu0
  have haM0 := bool_or_false_left hMasks0
  have hbM0 := bool_or_false_right hMasks0
  have hChiEq : bitAt (a.mask + b.mask + (a.val + b.val)) k = bitAt (a.val + b.val) k := by
    cases h1 : bitAt (a.mask + b.mask + (a.val + b.val)) k <;>
      cases h2 : bitAt (a.val + b.val) k <;>
      first | rfl | (rw [h1, h2] at hXor0; nomatch hXor0)
  rw [tnum_denote_iff_bitAt] at ha hb
  have hWfA : Nat.land a.val a.mask = 0 := Nat.eq_of_beq_eq_true ha.1
  have hWfB : Nat.land b.val b.mask = 0 := Nat.eq_of_beq_eq_true hb.1
  let ux := Nat.land x a.mask
  let uy := Nat.land y b.mask
  have hxEq : x = a.val + ux := by
    have hDisj : Nat.land a.val ux = 0 := by
      apply nat_eq_of_bitAt; intro j
      rw [bitAt_land, bitAt_land, bitAt_zero_nat]
      have hW := congrArg (fun z => bitAt z j) hWfA
      rw [bitAt_land, bitAt_zero_nat] at hW
      cases hav : bitAt a.val j with
      | false => rfl
      | true =>
        cases ham : bitAt a.mask j with
        | false => rw [Bool.and_false, Bool.and_false]
        | true => rw [hav, ham] at hW; nomatch hW
    have hLor : Nat.lor a.val ux = x := by
      apply nat_eq_of_bitAt; intro j
      rw [bitAt_lor, bitAt_land]
      cases hm : bitAt a.mask j with
      | false => rw [Bool.and_false, Bool.or_false]; exact (ha.2 j hm).symm
      | true =>
        have hW := congrArg (fun z => bitAt z j) hWfA
        rw [bitAt_land, bitAt_zero_nat, hm, Bool.and_true] at hW
        rw [hW, Bool.and_true, Bool.false_or]
    rw [nat_add_eq_lor_of_disjoint a.val ux hDisj, hLor]
  have hyEq : y = b.val + uy := by
    have hDisj : Nat.land b.val uy = 0 := by
      apply nat_eq_of_bitAt; intro j
      rw [bitAt_land, bitAt_land, bitAt_zero_nat]
      have hW := congrArg (fun z => bitAt z j) hWfB
      rw [bitAt_land, bitAt_zero_nat] at hW
      cases hbv : bitAt b.val j with
      | false => rfl
      | true =>
        cases hbm : bitAt b.mask j with
        | false => rw [Bool.and_false, Bool.and_false]
        | true => rw [hbv, hbm] at hW; nomatch hW
    have hLor : Nat.lor b.val uy = y := by
      apply nat_eq_of_bitAt; intro j
      rw [bitAt_lor, bitAt_land]
      cases hm : bitAt b.mask j with
      | false => rw [Bool.and_false, Bool.or_false]; exact (hb.2 j hm).symm
      | true =>
        have hW := congrArg (fun z => bitAt z j) hWfB
        rw [bitAt_land, bitAt_zero_nat, hm, Bool.and_true] at hW
        rw [hW, Bool.and_true, Bool.false_or]
    rw [nat_add_eq_lor_of_disjoint b.val uy hDisj, hLor]
  have huxBit0 : bitAt ux k = false := by
    dsimp only [ux]; rw [bitAt_land, haM0, Bool.and_false]
  have huyBit0 : bitAt uy k = false := by
    dsimp only [uy]; rw [bitAt_land, hbM0, Bool.and_false]
  have huxLe : Nat.mod ux P ≤ Nat.mod a.mask P := by
    apply nat_le_of_bitAt_imp; intro j hj
    rw [bitAt_mod_modPow2] at hj; rw [bitAt_mod_modPow2]
    cases hjk : Nat.blt j k with
    | false => rw [hjk] at hj; nomatch hj
    | true =>
      rw [hjk] at hj
      dsimp only [ux] at hj
      rw [bitAt_land] at hj
      exact bool_and_true_right hj
  have huyLe : Nat.mod uy P ≤ Nat.mod b.mask P := by
    apply nat_le_of_bitAt_imp; intro j hj
    rw [bitAt_mod_modPow2] at hj; rw [bitAt_mod_modPow2]
    cases hjk : Nat.blt j k with
    | false => rw [hjk] at hj; nomatch hj
    | true =>
      rw [hjk] at hj
      dsimp only [uy] at hj
      rw [bitAt_land] at hj
      exact bool_and_true_right hj
  have haLtP := tnum_prefix_disjoint_lt hWfA k
  have hbLtP := tnum_prefix_disjoint_lt hWfB k
  have hSvModLt : Nat.mod (a.val + b.val) P + (Nat.mod a.mask P + Nat.mod b.mask P) < 2 * P := by
    rw [mod_sum_mod_cancel a.val b.val P]
    cases Nat.lt_or_ge (Nat.mod a.val P + Nat.mod b.val P) P with
    | inl hSm =>
      have hEq : Nat.mod (Nat.mod a.val P + Nat.mod b.val P) P =
          Nat.mod a.val P + Nat.mod b.val P :=
        Nat.mod_eq_of_lt hSm
      rw [hEq]
      have hRe : (Nat.mod a.val P + Nat.mod b.val P) + (Nat.mod a.mask P + Nat.mod b.mask P) =
          (Nat.mod a.val P + Nat.mod a.mask P) + (Nat.mod b.val P + Nat.mod b.mask P) := by
        rw [Nat.add_assoc (Nat.mod a.val P) (Nat.mod b.val P),
            ← Nat.add_assoc (Nat.mod b.val P) (Nat.mod a.mask P),
            Nat.add_comm (Nat.mod b.val P) (Nat.mod a.mask P),
            Nat.add_assoc (Nat.mod a.mask P), ← Nat.add_assoc (Nat.mod a.val P)]
      rw [hRe, Nat.two_mul]
      exact Nat.add_lt_add haLtP hbLtP
    | inr hGe =>
      have haLo : Nat.mod a.val P < P := Nat.mod_lt _ hP
      have hbLo : Nat.mod b.val P < P := Nat.mod_lt _ hP
      have hSum2P : Nat.mod a.val P + Nat.mod b.val P < 2 * P := by
        rw [Nat.two_mul]; exact Nat.add_lt_add haLo hbLo
      have hSubMod : Nat.mod (Nat.mod a.val P + Nat.mod b.val P) P =
          (Nat.mod a.val P + Nat.mod b.val P) - P := by
        have hSubLt : (Nat.mod a.val P + Nat.mod b.val P) - P < P := by
          have hSubLe : (Nat.mod a.val P + Nat.mod b.val P) - P + P < P + P := by
            rw [Nat.sub_add_cancel hGe, ← Nat.two_mul]; exact hSum2P
          exact nat_lt_of_add_lt_add_right hSubLe
        have hModSub : Nat.mod (Nat.mod a.val P + Nat.mod b.val P) P =
            Nat.mod ((Nat.mod a.val P + Nat.mod b.val P) - P) P := Nat.mod_eq_sub_mod hGe
        have hModLt : Nat.mod ((Nat.mod a.val P + Nat.mod b.val P) - P) P =
            (Nat.mod a.val P + Nat.mod b.val P) - P := Nat.mod_eq_of_lt hSubLt
        rw [hModSub, hModLt]
      rw [hSubMod]
      have hBoth : (Nat.mod a.val P + Nat.mod a.mask P) +
          (Nat.mod b.val P + Nat.mod b.mask P) < 2 * P := by
        rw [Nat.two_mul]; exact Nat.add_lt_add haLtP hbLtP
      have hSumP : P + ((Nat.mod a.val P + Nat.mod b.val P) - P) =
          Nat.mod a.val P + Nat.mod b.val P := by
        rw [Nat.add_comm, Nat.sub_add_cancel hGe]
      have hTot : P + ((Nat.mod a.val P + Nat.mod b.val P - P) +
          (Nat.mod a.mask P + Nat.mod b.mask P)) < P + P := by
        rw [← Nat.add_assoc, hSumP]
        have hRe : (Nat.mod a.val P + Nat.mod b.val P) + (Nat.mod a.mask P + Nat.mod b.mask P) =
            (Nat.mod a.val P + Nat.mod a.mask P) + (Nat.mod b.val P + Nat.mod b.mask P) := by
          rw [Nat.add_assoc (Nat.mod a.val P) (Nat.mod b.val P),
              ← Nat.add_assoc (Nat.mod b.val P) (Nat.mod a.mask P),
              Nat.add_comm (Nat.mod b.val P) (Nat.mod a.mask P),
              Nat.add_assoc (Nat.mod a.mask P), ← Nat.add_assoc (Nat.mod a.val P)]
        rw [hRe, ← Nat.two_mul]; exact hBoth
      have hLessP := nat_lt_of_add_lt_add_left hTot
      rw [Nat.two_mul]
      exact Nat.lt_of_lt_of_le hLessP (Nat.le_add_right P P)
  have hmDecomp := nat_decomp_even_bit_zero haM0
  have hnDecomp := nat_decomp_even_bit_zero hbM0
  have huDecomp := nat_decomp_even_bit_zero huxBit0
  have hvDecomp := nat_decomp_even_bit_zero huyBit0
  have hPairAdd : ∀ q1 r1 q2 r2 : Nat,
      (2 * q1 * P + r1) + (2 * q2 * P + r2) = 2 * (q1 + q2) * P + (r1 + r2) := by
    intro q1 r1 q2 r2
    rw [Nat.mul_add 2 q1 q2, Nat.add_mul (2 * q1) (2 * q2) P]
    rw [Nat.add_assoc (2 * q1 * P) r1, ← Nat.add_assoc r1 (2 * q2 * P) r2,
        Nat.add_comm r1 (2 * q2 * P), Nat.add_assoc (2 * q2 * P) r1 r2,
        ← Nat.add_assoc (2 * q1 * P)]
  have hSmEq : a.mask + b.mask =
      2 * (Nat.div a.mask (2 * P) + Nat.div b.mask (2 * P)) * P +
        (Nat.mod a.mask P + Nat.mod b.mask P) := by
    have h1 := hPairAdd (Nat.div a.mask (2 * P)) (Nat.mod a.mask P)
                        (Nat.div b.mask (2 * P)) (Nat.mod b.mask P)
    rw [← hmDecomp, ← hnDecomp] at h1
    exact h1
  have hDUxUy : ux + uy =
      2 * (Nat.div ux (2 * P) + Nat.div uy (2 * P)) * P + (Nat.mod ux P + Nat.mod uy P) := by
    have h1 := hPairAdd (Nat.div ux (2 * P)) (Nat.mod ux P)
                        (Nat.div uy (2 * P)) (Nat.mod uy P)
    rw [← huDecomp, ← hvDecomp] at h1
    exact h1
  have hXY : x + y = (a.val + b.val) + (ux + uy) := by
    rw [hxEq, hyEq]
    rw [Nat.add_assoc a.val ux, ← Nat.add_assoc ux b.val uy,
        Nat.add_comm ux b.val, Nat.add_assoc b.val ux uy, ← Nat.add_assoc a.val b.val]
  have hSig : a.mask + b.mask + (a.val + b.val) = (a.val + b.val) + (a.mask + b.mask) :=
    Nat.add_comm (a.mask + b.mask) (a.val + b.val)
  have hSigMod := nat_div_mod2_shift_even (a.val + b.val)
    (Nat.div a.mask (2 * P) + Nat.div b.mask (2 * P)) k (Nat.mod a.mask P + Nat.mod b.mask P)
  rw [← hSmEq, ← hSig] at hSigMod
  have hXYMod := nat_div_mod2_shift_even (a.val + b.val)
    (Nat.div ux (2 * P) + Nat.div uy (2 * P)) k (Nat.mod ux P + Nat.mod uy P)
  rw [← hDUxUy, ← hXY] at hXYMod
  have hCarrySmZero :
      Nat.div (Nat.mod (a.val + b.val) P + (Nat.mod a.mask P + Nat.mod b.mask P)) P = 0 := by
    have hLt2 : Nat.div (Nat.mod (a.val + b.val) P + (Nat.mod a.mask P + Nat.mod b.mask P)) P < 2 :=
      (nat_div_lt_iff_lt_mul hP).2 hSvModLt
    cases hc : Nat.div (Nat.mod (a.val + b.val) P + (Nat.mod a.mask P + Nat.mod b.mask P)) P with
    | zero => rfl
    | succ c' =>
      cases c' with
      | zero =>
        dsimp only [bitAt] at hChiEq
        rw [hSigMod, hc] at hChiEq
        have hq := Nat.div_add_mod (Nat.div (a.val + b.val) P) 2
        dsimp only [HDiv.hDiv, Div.div, HMod.hMod, Mod.mod] at hq
        cases hM : Nat.mod (Nat.div (a.val + b.val) P) 2 with
        | zero =>
          rw [hM, Nat.add_zero] at hq
          have hSucc : Nat.div (a.val + b.val) P + 1 =
              2 * Nat.div (Nat.div (a.val + b.val) P) 2 + 1 :=
            congrArg (fun z => z + 1) hq.symm
          rw [hSucc, mod2_two_mul_add_one, hM] at hChiEq
          nomatch hChiEq
        | succ r =>
          cases r with
          | zero =>
            rw [hM] at hq
            have hSucc : Nat.div (a.val + b.val) P + 1 =
                2 * (Nat.div (Nat.div (a.val + b.val) P) 2 + 1) := by
              have hS1 : Nat.div (a.val + b.val) P + 1 =
                  (2 * Nat.div (Nat.div (a.val + b.val) P) 2 + 1) + 1 :=
                congrArg (fun z => z + 1) hq.symm
              rw [Nat.add_assoc, show (1 + 1 = 2 * 1) from rfl, ← Nat.mul_add] at hS1
              exact hS1
            rw [hSucc, mod2_two_mul, hM] at hChiEq
            nomatch hChiEq
          | succ r' =>
            have hLt2q : Nat.mod (Nat.div (a.val + b.val) P) 2 < 2 :=
              Nat.mod_lt _ (Nat.zero_lt_succ 1)
            rw [hM] at hLt2q
            nomatch (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hLt2q))
      | succ c'' =>
        rw [hc] at hLt2
        nomatch (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hLt2))
  have hLeD : Nat.mod (a.val + b.val) P + (Nat.mod ux P + Nat.mod uy P) ≤
      Nat.mod (a.val + b.val) P + (Nat.mod a.mask P + Nat.mod b.mask P) :=
    Nat.add_le_add_left (Nat.add_le_add huxLe huyLe) _
  have hCarryDZero : Nat.div (Nat.mod (a.val + b.val) P + (Nat.mod ux P + Nat.mod uy P)) P = 0 := by
    have hLtP : Nat.mod (a.val + b.val) P + (Nat.mod ux P + Nat.mod uy P) < P := by
      cases Nat.lt_or_ge (Nat.mod (a.val + b.val) P + (Nat.mod a.mask P + Nat.mod b.mask P)) P with
      | inl hLt => exact Nat.lt_of_le_of_lt hLeD hLt
      | inr hGe =>
        have hGeDiv :
            1 ≤ Nat.div (Nat.mod (a.val + b.val) P +
              (Nat.mod a.mask P + Nat.mod b.mask P)) P := by
          have h := (Nat.le_div_iff_mul_le hP).2 (by rw [Nat.one_mul]; exact hGe)
          dsimp only [HDiv.hDiv, Div.div] at h; exact h
        rw [hCarrySmZero] at hGeDiv
        nomatch hGeDiv
    exact Nat.div_eq_of_lt hLtP
  dsimp only [bitAt]
  rw [hXYMod, hCarryDZero, Nat.add_zero]

/-- Soundness of `Tnum.add` over `w`-bit modular addition. -/
theorem tnum_add_sound {w : Nat} {a b : Tnum} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) :
    (Tnum.add w a b).denote (wrapVal w (x + y)) := by
  rw [tnum_denote_iff_bitAt]
  dsimp only [Tnum.add, wrapVal, Tnum.wf]
  let muRaw := Nat.lor (Nat.xor (a.mask + b.mask + (a.val + b.val))
    (a.val + b.val)) (Nat.lor a.mask b.mask)
  let mu := Nat.mod muRaw (modPow2 w)
  let sv := a.val + b.val
  refine ⟨?_, ?_⟩
  · apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro k
    rw [bitAt_land, bitAt_mod_modPow2, bitAt_mod_modPow2, bitAt_zero_nat]
    cases hkw : Nat.blt k w with
    | false => rfl
    | true =>
      dsimp only
      rw [bitAt_andNot, bitAt_mod_modPow2, hkw]
      dsimp only
      cases bitAt sv k <;> cases bitAt muRaw k <;> rfl
  · intro k hmk0
    rw [bitAt_mod_modPow2] at hmk0
    rw [bitAt_mod_modPow2, bitAt_mod_modPow2]
    cases hkw : Nat.blt k w with
    | false => rfl
    | true =>
      rw [hkw] at hmk0
      dsimp only [muRaw] at hmk0
      have hBitEq := tnum_add_bit_helper ha hb k hmk0
      rw [bitAt_andNot, bitAt_mod_modPow2, hkw, hmk0, Bool.not_false, Bool.and_true]
      exact hBitEq

/-- One's-complement identity `x + (x ^^^ (2^w - 1)) = 2^w - 1` for `x < 2^w`.
-/
theorem tnum_xor_allOnes_add {x w : Nat} (hx : x < modPow2 w) :
    x + Nat.xor x (modPow2 w - 1) = modPow2 w - 1 := by
  have hDisj : Nat.land x (Nat.xor x (modPow2 w - 1)) = 0 := by
    apply nat_eq_of_bitAt; intro k
    rw [bitAt_land, bitAt_xor, bitAt_modPow2_sub_one, bitAt_zero_nat]
    cases hkw : Nat.blt k w with
    | true => cases bitAt x k <;> rfl
    | false =>
      have hNot : ¬ (k < w) := fun h => by
        have ht := blt_true_of_lt h; rw [ht] at hkw; nomatch hkw
      rw [bitAt_zero_ge_of_lt_modPow2 hx k (Nat.le_of_not_lt hNot)]
      rfl
  have hLor : Nat.lor x (Nat.xor x (modPow2 w - 1)) = modPow2 w - 1 := by
    apply nat_eq_of_bitAt; intro k
    rw [bitAt_lor, bitAt_xor, bitAt_modPow2_sub_one]
    cases hkw : Nat.blt k w with
    | true => cases bitAt x k <;> rfl
    | false =>
      have hNot : ¬ (k < w) := fun h => by
        have ht := blt_true_of_lt h; rw [ht] at hkw; nomatch hkw
      rw [bitAt_zero_ge_of_lt_modPow2 hx k (Nat.le_of_not_lt hNot)]
      rfl
  rw [nat_add_eq_lor_of_disjoint x _ hDisj, hLor]

/-- Soundness of `Tnum.neg` over `w`-bit modular negation. -/
theorem tnum_neg_sound {w : Nat} {a : Tnum} {x : Nat}
    (ha : a.denote x) (hx : x < modPow2 w) :
    (Tnum.neg w a).denote (wrapVal w (modPow2 w - x)) := by
  dsimp only [Tnum.neg]
  let y := Nat.xor x (modPow2 w - 1)
  have hyLt : y < modPow2 w := by
    have hAdd := tnum_xor_allOnes_add hx
    have hLe : y ≤ modPow2 w - 1 := by rw [← hAdd]; exact Nat.le_add_left y x
    exact Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos w) (Nat.zero_lt_succ 0))
  have haRaw : Tnum.denote ⟨wrapVal w (andNot (Nat.xor a.val (modPow2 w - 1)) a.mask),
                            wrapVal w a.mask⟩ y := by
    rw [tnum_denote_iff_bitAt]
    rw [tnum_denote_iff_bitAt] at ha
    dsimp only [Tnum.wf, wrapVal]
    refine ⟨?_, ?_⟩
    · apply nat_beq_of_eq; apply nat_eq_of_bitAt; intro k
      rw [bitAt_land, bitAt_mod_modPow2, bitAt_mod_modPow2, bitAt_zero_nat]
      cases Nat.blt k w with
      | false => rfl
      | true =>
        rw [bitAt_andNot]
        cases bitAt (Nat.xor a.val (modPow2 w - 1)) k <;> cases bitAt a.mask k <;> rfl
    · intro k hmk0
      rw [bitAt_mod_modPow2] at hmk0
      rw [bitAt_mod_modPow2]
      cases hkw : Nat.blt k w with
      | false =>
        exact bitAt_zero_ge_of_lt_modPow2 hyLt k
          (Nat.le_of_not_lt fun h => by rw [blt_true_of_lt h] at hkw; nomatch hkw)
      | true =>
        rw [hkw] at hmk0
        dsimp only at hmk0
        rw [bitAt_andNot, hmk0, Bool.not_false, Bool.and_true, bitAt_xor, bitAt_xor, ha.2 k hmk0]
  have hc1 := tnum_const_wrap_sound (w := w) (c := 1)
  have hAddRes := tnum_add_sound (w := w) haRaw hc1
  have hWrapEq : wrapVal w (y + wrapVal w 1) = wrapVal w (modPow2 w - x) := by
    dsimp only [wrapVal]
    let M := modPow2 w
    have hM : 0 < M := modPow2_pos w
    have h1 := mod_sum_mod_cancel y (Nat.mod 1 M) M
    have h2 := mod_sum_mod_cancel y 1 M
    have hModIdem : Nat.mod (Nat.mod 1 M) M = Nat.mod 1 M := Nat.mod_eq_of_lt (Nat.mod_lt 1 hM)
    rw [hModIdem] at h1
    have hSumMod : Nat.mod (y + Nat.mod 1 M) M = Nat.mod (y + 1) M := Eq.trans h1 h2.symm
    have hSum1 : x + (y + 1) = M := by
      rw [← Nat.add_assoc, tnum_xor_allOnes_add hx, Nat.sub_add_cancel hM]
    have hSum2 : x + (M - x) = M := by
      rw [Nat.add_comm]; exact Nat.sub_add_cancel (Nat.le_of_lt hx)
    have hyEq : y + 1 = M - x := Nat.add_left_cancel (Eq.trans hSum1 hSum2.symm)
    rw [hSumMod, hyEq]
  rw [hWrapEq] at hAddRes
  exact hAddRes

/-- Soundness of `Tnum.sub` over `w`-bit modular subtraction. -/
theorem tnum_sub_sound {w : Nat} {a b : Tnum} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) (hy : y < modPow2 w) :
    (Tnum.sub w a b).denote (wrapVal w (modPow2 w + x - y)) := by
  dsimp only [Tnum.sub]
  have hNeg := tnum_neg_sound hb hy
  have hAdd := tnum_add_sound (w := w) ha hNeg
  have hEq : wrapVal w (x + wrapVal w (modPow2 w - y)) = wrapVal w (modPow2 w + x - y) := by
    dsimp only [wrapVal]
    let M := modPow2 w
    have hM : 0 < M := modPow2_pos w
    rw [Nat.add_comm x (Nat.mod (M - y) M)]
    have hModSum : Nat.mod (Nat.mod (M - y) M + x) M = Nat.mod (M - y + x) M := by
      have h1 := mod_sum_mod_cancel (M - y) x M
      have h2 := mod_sum_mod_cancel (Nat.mod (M - y) M) x M
      have hModIdem : Nat.mod (Nat.mod (M - y) M) M = Nat.mod (M - y) M :=
        Nat.mod_eq_of_lt (Nat.mod_lt _ hM)
      rw [hModIdem] at h2
      rw [h2, ← h1]
    rw [hModSum]
    have hSubAssoc : M - y + x = M + x - y := by
      have hLe : y ≤ M := Nat.le_of_lt hy
      have h1 : (M - y + x) + y = M + x := by
        rw [Nat.add_assoc (M - y) x y, Nat.add_comm x y, ← Nat.add_assoc (M - y) y x,
            Nat.sub_add_cancel hLe]
      have hLe2 : y ≤ M + x := Nat.le_trans hLe (Nat.le_add_right M x)
      have h2 : (M + x - y) + y = M + x := Nat.sub_add_cancel hLe2
      exact Nat.add_right_cancel (Eq.trans h1 h2.symm)
    rw [hSubAssoc]
  rw [hEq] at hAdd
  exact hAdd

end Anneal.AiPcc

end
