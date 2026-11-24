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
# Wrapped Intervals and Strided Congruences (`Anneal.AiPcc.WrappedInterval`)

Constructive Pass-1 `WrappedInterval` (straddling modular arcs `[lo, hi]` over
`[0, 2^w - 1]` with `WrappedInterval.add`, `sub`, `meet`, and `join`) and
`StridedCong` (`Nat.mod x m = r` alignment and stride tracking with
`StridedCong.wrapAdd` and `wrapSub`), compiled independently of
`Anneal.AiPcc.Tnum`.
-/

/-! ### `WrappedInterval` (Straddling Modular Arcs) -/

/-- Wrapped modular interval over `Z / M Z`: `.bot` (empty), `.top` (full ring
`[0, M)`), or clockwise arc `.iv lo hi`. -/
inductive WrappedInterval where
  | bot
  | top
  | iv (lo hi : Nat)

/-- Endpoint well-formedness (`lo < M` and `hi < M` on `.iv lo hi`). -/
@[expose] def WrappedInterval.wf (M : Nat) : WrappedInterval → Bool
  | .bot => true
  | .top => true
  | .iv lo hi => Nat.blt lo M && Nat.blt hi M

/-- Clockwise modular arc length from `lo` to `hi` modulo `M`. -/
@[expose] def wrapSpan (M lo hi : Nat) : Nat :=
  match Nat.ble lo hi with
  | true => hi - lo
  | false => M - lo + hi

/-- Concretization of `wi` over `[0, M)` (`lo ≤ x ≤ hi` when `lo ≤ hi`, or `lo ≤
x ∨ x ≤ hi` when straddling `0`). -/
@[expose] def WrappedInterval.denote (M : Nat) (wi : WrappedInterval) (x : Nat)
    : Prop :=
  match wi with
  | .bot => False
  | .top => x < M
  | .iv lo hi =>
    lo < M ∧ hi < M ∧ x < M ∧
    match Nat.ble lo hi with
    | true => lo ≤ x ∧ x ≤ hi
    | false => lo ≤ x ∨ x ≤ hi

/-- `wrapSpan M lo hi < M` for in-range endpoints `lo, hi < M`. -/
theorem wrapSpan_lt {M lo hi : Nat} (hLo : lo < M) (hHi : hi < M) :
    wrapSpan M lo hi < M := by
  dsimp only [wrapSpan]
  cases hBle : Nat.ble lo hi with
  | true => exact Nat.lt_of_le_of_lt (Nat.sub_le hi lo) hHi
  | false =>
    have hNot : ¬ (lo ≤ hi) := fun h => by
      have ht := Nat.ble_eq_true_of_le h; rw [ht] at hBle; nomatch hBle
    have hGt : hi < lo := Nat.lt_of_not_le hNot
    have hSumLe : hi + (M - lo) < lo + (M - lo) := Nat.add_lt_add_right hGt (M - lo)
    rw [Nat.add_comm lo (M - lo), Nat.sub_add_cancel (Nat.le_of_lt hLo),
        Nat.add_comm hi (M - lo)] at hSumLe
    exact hSumLe

/-- Clockwise offset characterization `x ∈ .iv lo hi ↔ ∃ d ≤ wrapSpan M lo hi, x
= (lo + d) mod M`. -/
theorem wrapped_denote_iff_offset {M lo hi x : Nat}
    (hLo : lo < M) (hHi : hi < M) (hx : x < M) :
    WrappedInterval.denote M (.iv lo hi) x ↔
      ∃ d : Nat, d ≤ wrapSpan M lo hi ∧ x = Nat.mod (lo + d) M := by
  dsimp only [WrappedInterval.denote, wrapSpan]
  cases hBle : Nat.ble lo hi with
  | true =>
    have hLe : lo ≤ hi := Nat.le_of_ble_eq_true hBle
    constructor
    · intro h
      have hxLo := h.2.2.2.1
      have hxHi := h.2.2.2.2
      refine ⟨x - lo, Nat.sub_le_sub_right hxHi lo, ?_⟩
      have hAdd : lo + (x - lo) = x := by rw [Nat.add_comm]; exact Nat.sub_add_cancel hxLo
      rw [hAdd, nat_mod_eq_of_lt hx]
    · intro h
      refine ⟨hLo, hHi, hx, ?_⟩
      cases h with
      | intro d hd =>
        have hBound : lo + d < M :=
          Nat.lt_of_le_of_lt (Nat.add_le_add_left hd.1 lo)
            (by rw [Nat.add_comm lo (hi - lo), Nat.sub_add_cancel hLe]; exact hHi)
        have hEq : x = lo + d := by rw [hd.2, nat_mod_eq_of_lt hBound]
        rw [hEq]
        refine ⟨Nat.le_add_right lo d, ?_⟩
        have h2 := Nat.add_le_add_left hd.1 lo
        rw [Nat.add_comm lo (hi - lo), Nat.sub_add_cancel hLe] at h2
        exact h2
  | false =>
    have hNot : ¬ (lo ≤ hi) := fun h => by
      have ht := Nat.ble_eq_true_of_le h; rw [ht] at hBle; nomatch hBle
    have hGt : hi < lo := Nat.lt_of_not_le hNot
    have hLoLeM : lo ≤ M := Nat.le_of_lt hLo
    constructor
    · intro h
      cases h.2.2.2 with
      | inl hUpper =>
        refine ⟨x - lo, ?_, ?_⟩
        · have h1 : x - lo ≤ M - lo := Nat.sub_le_sub_right (Nat.le_of_lt hx) lo
          exact Nat.le_trans h1 (Nat.le_add_right (M - lo) hi)
        · have h1 : lo + (x - lo) = x := by rw [Nat.add_comm]; exact Nat.sub_add_cancel hUpper
          rw [h1, nat_mod_eq_of_lt hx]
      | inr hLower =>
        refine ⟨(M - lo) + x, Nat.add_le_add_left hLower (M - lo), ?_⟩
        have h1 : lo + (M - lo + x) = M + x := by
          rw [← Nat.add_assoc, Nat.add_comm lo (M - lo), Nat.sub_add_cancel hLoLeM]
        rw [h1, nat_add_mod_self_left, nat_mod_eq_of_lt hx]
    · intro h
      refine ⟨hLo, hHi, hx, ?_⟩
      cases h with
      | intro d hd =>
        cases Nat.lt_or_ge (lo + d) M with
        | inl hNoWrap =>
          left
          have hEq : x = lo + d := by rw [hd.2, nat_mod_eq_of_lt hNoWrap]
          rw [hEq]
          exact Nat.le_add_right lo d
        | inr hWrap =>
          right
          have hUp : lo + d ≤ M + hi := by
            have h1 := Nat.add_le_add_left hd.1 lo
            rw [← Nat.add_assoc, Nat.add_comm lo (M - lo), Nat.sub_add_cancel hLoLeM] at h1
            exact h1
          have hSubLeHi : lo + d - M ≤ hi := by
            have h1 : (lo + d - M) + M ≤ hi + M := by
              rw [Nat.sub_add_cancel hWrap, Nat.add_comm hi M]; exact hUp
            exact Nat.le_of_add_le_add_right h1
          have hSubLtM : lo + d - M < M := Nat.lt_of_le_of_lt hSubLeHi hHi
          have hEqMod : Nat.mod (lo + d) M = lo + d - M := by
            rw [nat_mod_eq_sub_mod hWrap, nat_mod_eq_of_lt hSubLtM]
          rw [hd.2, hEqMod]
          exact hSubLeHi

/-- Clockwise endpoint `(lo + s) mod M` has exact span `s` when `s < M`. -/
theorem wrapped_span_of_add_lt {M lo s : Nat} (hM : 0 < M) (hLo : lo < M) (hs : s < M) :
    let hi := Nat.mod (lo + s) M
    hi < M ∧ wrapSpan M lo hi = s := by
  dsimp only
  have hHiLt : Nat.mod (lo + s) M < M := Nat.mod_lt _ hM
  refine ⟨hHiLt, ?_⟩
  cases Nat.lt_or_ge (lo + s) M with
  | inl hLt =>
    have hHiEq : Nat.mod (lo + s) M = lo + s := nat_mod_eq_of_lt hLt
    rw [hHiEq]
    dsimp only [wrapSpan]
    have hBle : Nat.ble lo (lo + s) = true := Nat.ble_eq_true_of_le (Nat.le_add_right lo s)
    rw [hBle, Nat.add_comm lo s, Nat.add_sub_cancel]
  | inr hGe =>
    have hSubLtM : lo + s - M < M := by
      have hSumLt : lo + s < M + M := Nat.add_lt_add hLo hs
      have h1 : (lo + s - M) + M < M + M := by rw [Nat.sub_add_cancel hGe]; exact hSumLt
      exact nat_lt_of_add_lt_add_right h1
    have hHiEq : Nat.mod (lo + s) M = lo + s - M := by
      rw [nat_mod_eq_sub_mod hGe, nat_mod_eq_of_lt hSubLtM]
    rw [hHiEq]
    have hHiLtLo : lo + s - M < lo := by
      have h1 : (lo + s - M) + M < lo + M := by
        rw [Nat.sub_add_cancel hGe]; exact Nat.add_lt_add_left hs lo
      exact nat_lt_of_add_lt_add_right h1
    dsimp only [wrapSpan]
    have hBle : Nat.ble lo (lo + s - M) = false := by
      cases hb : Nat.ble lo (lo + s - M) with
      | false => rfl
      | true => exact False.elim (Nat.not_le_of_gt hHiLtLo (Nat.le_of_ble_eq_true hb))
    rw [hBle]
    have hAdd1 : M - lo + (lo + s - M) + lo = s + lo := by
      have h2 : M - lo + lo = M := Nat.sub_add_cancel (Nat.le_of_lt hLo)
      rw [Nat.add_comm (M - lo) (lo + s - M), Nat.add_assoc (lo + s - M) (M - lo) lo,
          h2, Nat.sub_add_cancel hGe, Nat.add_comm lo s]
    exact Nat.add_right_cancel hAdd1

/-- `(lo + wrapSpan M lo hi) mod M = hi` for `lo, hi < M`. -/
theorem wrapped_hi_eq_mod_lo_span {M lo hi : Nat} (hLo : lo < M) (hHi : hi < M) :
    Nat.mod (lo + wrapSpan M lo hi) M = hi := by
  dsimp only [wrapSpan]
  cases hBle : Nat.ble lo hi with
  | true =>
    have hLe := Nat.le_of_ble_eq_true hBle
    rw [Nat.add_comm lo (hi - lo), Nat.sub_add_cancel hLe]
    exact nat_mod_eq_of_lt hHi
  | false =>
    rw [← Nat.add_assoc, Nat.add_comm lo (M - lo), Nat.sub_add_cancel (Nat.le_of_lt hLo),
        nat_add_mod_self_left]
    exact nat_mod_eq_of_lt hHi

/-- Singleton wrapped interval `[c mod M, c mod M]`. -/
@[expose] def WrappedInterval.const (M c : Nat) : WrappedInterval :=
  match Nat.beq M 0 with
  | true => .bot
  | false =>
    let v := Nat.mod c M
    .iv v v

private theorem wrappedInterval_denote_of_full_span {M lo2 hi2 x : Nat}
    (hM : 0 < M) (hLo2 : lo2 < M) (hHi2 : hi2 < M) (hx : x < M)
    (hSpan : wrapSpan M lo2 hi2 = M - 1) :
    WrappedInterval.denote M (.iv lo2 hi2) x := by
  rw [wrapped_denote_iff_offset hLo2 hHi2 hx]
  let d := Nat.mod (M + x - lo2) M
  have hdLt : d < M := Nat.mod_lt _ hM
  have hdLe : d ≤ wrapSpan M lo2 hi2 := by
    rw [hSpan]
    cases M with
    | zero => nomatch hM
    | succ m' => exact Nat.le_of_lt_succ hdLt
  refine ⟨d, hdLe, ?_⟩
  have hModEq : Nat.mod (lo2 + d) M = x := by
    dsimp only [d]
    have h1 := mod_sum_mod_cancel lo2 (M + x - lo2) M
    have h2 := mod_sum_mod_cancel lo2 (Nat.mod (M + x - lo2) M) M
    have hIdem : Nat.mod (Nat.mod (M + x - lo2) M) M = Nat.mod (M + x - lo2) M :=
      nat_mod_eq_of_lt (Nat.mod_lt _ hM)
    rw [hIdem] at h2
    have hEq := Eq.trans h2 h1.symm
    rw [hEq]
    have hSub : lo2 + (M + x - lo2) = M + x := by
      have hLeM : lo2 ≤ M + x :=
        Nat.le_trans (Nat.le_of_lt hLo2) (Nat.le_add_right M x)
      rw [Nat.add_comm]; exact Nat.sub_add_cancel hLeM
    rw [hSub, nat_add_mod_self_left, nat_mod_eq_of_lt hx]
  exact hModEq.symm

/-- Decidable inclusion check on `WrappedInterval` (treating full-span `wrapSpan
== M - 1` arcs equivalently to `.top`). -/
@[expose] def WrappedInterval.le (M : Nat) (a b : WrappedInterval) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .top => true
  | .top, .iv lo2 hi2 =>
    Nat.blt lo2 M && Nat.blt hi2 M && Nat.beq (wrapSpan M lo2 hi2) (M - 1)
  | .iv lo1 hi1, .iv lo2 hi2 =>
    Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M &&
      (Nat.beq (wrapSpan M lo2 hi2) (M - 1) ||
        let off := Nat.mod (M + lo1 - lo2) M
        Nat.ble (off + wrapSpan M lo1 hi1) (wrapSpan M lo2 hi2))
  | _, _ => false

/-- Soundness of `WrappedInterval.le`. -/
theorem wrappedInterval_le_sound {M : Nat} (hM : 0 < M) {a b : WrappedInterval} {x : Nat}
    (hLe : WrappedInterval.le M a b = true) (ha : a.denote M x) : b.denote M x := by
  cases a with
  | bot => exact False.elim ha
  | top =>
    cases b with
    | top => exact ha
    | bot => nomatch hLe
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.le] at hLe
      have h12 := bool_and_true_left hLe
      have hLo2Lt : lo2 < M := lt_of_blt_true (bool_and_true_left h12)
      have hHi2Lt : hi2 < M := lt_of_blt_true (bool_and_true_right h12)
      have hSpan : wrapSpan M lo2 hi2 = M - 1 :=
        Nat.eq_of_beq_eq_true (bool_and_true_right hLe)
      exact wrappedInterval_denote_of_full_span hM hLo2Lt hHi2Lt ha hSpan
  | iv lo1 hi1 =>
    cases b with
    | bot => nomatch hLe
    | top => exact ha.2.2.1
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.le] at hLe
      have hLo1Lt : lo1 < M := ha.1
      have hHi1Lt : hi1 < M := ha.2.1
      have hxLt : x < M := ha.2.2.1
      have h1234 := bool_and_true_left hLe
      have h123 := bool_and_true_left h1234
      have h12 := bool_and_true_left h123
      have hLo2Lt : lo2 < M := lt_of_blt_true (bool_and_true_right h123)
      have hHi2Lt : hi2 < M := lt_of_blt_true (bool_and_true_right h1234)
      have hOr := bool_and_true_right hLe
      cases hFull : Nat.beq (wrapSpan M lo2 hi2) (M - 1) with
      | true =>
        exact wrappedInterval_denote_of_full_span hM hLo2Lt hHi2Lt hxLt
          (Nat.eq_of_beq_eq_true hFull)
      | false =>
        rw [hFull] at hOr
        have hSpanLe : Nat.mod (M + lo1 - lo2) M + wrapSpan M lo1 hi1 ≤ wrapSpan M lo2 hi2 :=
          Nat.le_of_ble_eq_true hOr
        have hxOff := (wrapped_denote_iff_offset hLo1Lt hHi1Lt hxLt).1 ha
        cases hxOff with
        | intro d1 hd1 =>
          rw [wrapped_denote_iff_offset hLo2Lt hHi2Lt hxLt]
          let off := Nat.mod (M + lo1 - lo2) M
          refine ⟨off + d1, Nat.le_trans (Nat.add_le_add_left hd1.1 off) hSpanLe, ?_⟩
          have hLo1Eq : Nat.mod (lo2 + off) M = lo1 := by
            dsimp only [off]
            have h1 := mod_sum_mod_cancel lo2 (M + lo1 - lo2) M
            have h2 := mod_sum_mod_cancel lo2 (Nat.mod (M + lo1 - lo2) M) M
            have hIdem : Nat.mod (Nat.mod (M + lo1 - lo2) M) M = Nat.mod (M + lo1 - lo2) M :=
              nat_mod_eq_of_lt (Nat.mod_lt _ hM)
            rw [hIdem] at h2
            have hEq := Eq.trans h2 h1.symm
            rw [hEq]
            have hSub : lo2 + (M + lo1 - lo2) = M + lo1 := by
              have hLeM : lo2 ≤ M + lo1 :=
                Nat.le_trans (Nat.le_of_lt hLo2Lt) (Nat.le_add_right M lo1)
              rw [Nat.add_comm]; exact Nat.sub_add_cancel hLeM
            rw [hSub, nat_add_mod_self_left, nat_mod_eq_of_lt hLo1Lt]
          rw [hd1.2, ← Nat.add_assoc lo2 off d1, mod_sum_mod_cancel (lo2 + off) d1 M, hLo1Eq]
          have hSumC := mod_sum_mod_cancel lo1 d1 M
          rw [nat_mod_eq_of_lt hLo1Lt] at hSumC
          exact hSumC

/-- Modular arc addition on `WrappedInterval` (normalizing full-ring spans to
`.top`). -/
@[expose] def WrappedInterval.add (M : Nat) (a b : WrappedInterval) :
    WrappedInterval :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .iv lo1 hi1, .iv lo2 hi2 =>
    match Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M with
    | false => .top
    | true =>
      let s := wrapSpan M lo1 hi1 + wrapSpan M lo2 hi2
      match Nat.blt s (M - 1) with
      | false => .top
      | true =>
        let lo := Nat.mod (lo1 + lo2) M
        .iv lo (Nat.mod (lo + s) M)

/-- Soundness of `WrappedInterval.add` modulo `M`. -/
theorem wrappedInterval_add_sound {M : Nat} (hM : 0 < M) {a b : WrappedInterval} {x y : Nat}
    (ha : a.denote M x) (hb : b.denote M y) :
    (WrappedInterval.add M a b).denote M (Nat.mod (x + y) M) := by
  cases a with
  | bot => exact False.elim ha
  | top =>
    cases b with
    | bot => exact False.elim hb
    | top => exact Nat.mod_lt _ hM
    | iv _ _ => exact Nat.mod_lt _ hM
  | iv lo1 hi1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact Nat.mod_lt _ hM
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.add]
      have hWf : (Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M) = true := by
        rw [blt_true_of_lt ha.1, blt_true_of_lt ha.2.1,
            blt_true_of_lt hb.1, blt_true_of_lt hb.2.1]; rfl
      rw [hWf]
      dsimp only
      let s := wrapSpan M lo1 hi1 + wrapSpan M lo2 hi2
      cases hs : Nat.blt s (M - 1) with
      | false => exact Nat.mod_lt _ hM
      | true =>
        dsimp only
        have hsLt : s < M := Nat.lt_of_lt_of_le (lt_of_blt_true hs) (Nat.sub_le M 1)
        have hLoLt : Nat.mod (lo1 + lo2) M < M := Nat.mod_lt _ hM
        have hSpan := wrapped_span_of_add_lt hM hLoLt hsLt
        have hxOff := (wrapped_denote_iff_offset ha.1 ha.2.1 ha.2.2.1).1 ha
        have hyOff := (wrapped_denote_iff_offset hb.1 hb.2.1 hb.2.2.1).1 hb
        rw [wrapped_denote_iff_offset hLoLt hSpan.1 (nat_mod_lt (x + y) hM)]
        cases hxOff with
        | intro d1 hd1 =>
          cases hyOff with
          | intro d2 hd2 =>
            refine ⟨d1 + d2, ?_, ?_⟩
            · rw [hSpan.2]; exact Nat.add_le_add hd1.1 hd2.1
            · rw [hd1.2, hd2.2, ← mod_sum_mod_cancel (lo1 + d1) (lo2 + d2) M]
              have hRearr : (lo1 + d1) + (lo2 + d2) = (lo1 + lo2) + (d1 + d2) := by
                rw [Nat.add_assoc lo1 d1 (lo2 + d2), ← Nat.add_assoc d1 lo2 d2, Nat.add_comm d1 lo2,
                    Nat.add_assoc lo2 d1 d2, ← Nat.add_assoc lo1 lo2 (d1 + d2)]
              rw [hRearr, mod_sum_mod_cancel (lo1 + lo2) (d1 + d2) M]
              have hIdem : Nat.mod (Nat.mod (lo1 + lo2) M) M = Nat.mod (lo1 + lo2) M :=
                nat_mod_eq_of_lt hLoLt
              have hBack := mod_sum_mod_cancel (Nat.mod (lo1 + lo2) M) (d1 + d2) M
              rw [hIdem] at hBack
              rw [← hBack]

/-- Modular arc subtraction on `WrappedInterval`. -/
@[expose] def WrappedInterval.sub (M : Nat) (a b : WrappedInterval) :
    WrappedInterval :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .iv lo1 hi1, .iv lo2 hi2 =>
    match Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M with
    | false => .top
    | true =>
      let s := wrapSpan M lo1 hi1 + wrapSpan M lo2 hi2
      match Nat.blt s (M - 1) with
      | false => .top
      | true =>
        let lo := Nat.mod (M + lo1 - hi2) M
        .iv lo (Nat.mod (lo + s) M)

/-- Soundness of `WrappedInterval.sub` modulo `M`. -/
theorem wrappedInterval_sub_sound {M : Nat} (hM : 0 < M) {a b : WrappedInterval} {x y : Nat}
    (ha : a.denote M x) (hb : b.denote M y) :
    (WrappedInterval.sub M a b).denote M (Nat.mod (M + x - y) M) := by
  cases a with
  | bot => exact False.elim ha
  | top =>
    cases b with
    | bot => exact False.elim hb
    | top => exact Nat.mod_lt _ hM
    | iv _ _ => exact Nat.mod_lt _ hM
  | iv lo1 hi1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact Nat.mod_lt _ hM
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.sub]
      have hWf : (Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M) = true := by
        rw [blt_true_of_lt ha.1, blt_true_of_lt ha.2.1,
            blt_true_of_lt hb.1, blt_true_of_lt hb.2.1]; rfl
      rw [hWf]
      dsimp only
      let s := wrapSpan M lo1 hi1 + wrapSpan M lo2 hi2
      cases hs : Nat.blt s (M - 1) with
      | false => exact Nat.mod_lt _ hM
      | true =>
        dsimp only
        have hsLt : s < M := Nat.lt_of_lt_of_le (lt_of_blt_true hs) (Nat.sub_le M 1)
        have hLoLt : Nat.mod (M + lo1 - hi2) M < M := Nat.mod_lt _ hM
        have hSpan := wrapped_span_of_add_lt hM hLoLt hsLt
        have hxOff := (wrapped_denote_iff_offset ha.1 ha.2.1 ha.2.2.1).1 ha
        have hyOff := (wrapped_denote_iff_offset hb.1 hb.2.1 hb.2.2.1).1 hb
        rw [wrapped_denote_iff_offset hLoLt hSpan.1 (nat_mod_lt (M + x - y) hM)]
        cases hxOff with
        | intro d1 hd1 =>
          cases hyOff with
          | intro d2 hd2 =>
            let s2 := wrapSpan M lo2 hi2
            refine ⟨d1 + (s2 - d2), ?_, ?_⟩
            · rw [hSpan.2]; exact Nat.add_le_add hd1.1 (Nat.sub_le s2 d2)
            · have hyMod : Nat.mod (y + (s2 - d2)) M = hi2 := by
                have hHiEq := wrapped_hi_eq_mod_lo_span hb.1 hb.2.1
                rw [hd2.2, mod_add_mod_left (lo2 + d2) (s2 - d2) M hM,
                    Nat.add_assoc lo2 d2 (s2 - d2), Nat.add_comm d2 (s2 - d2),
                    Nat.sub_add_cancel hd2.1]
                exact hHiEq
              have hyLeM : y ≤ M := Nat.le_of_lt hb.2.2.1
              have hHi2LeM : hi2 ≤ M + lo1 :=
                Nat.le_trans (Nat.le_of_lt hb.2.1) (Nat.le_add_right M lo1)
              have hSumTarget : Nat.mod (Nat.mod (M + x - y) M + y) M = x := by
                rw [mod_add_mod_left (M + x - y) y M hM,
                    Nat.sub_add_cancel (Nat.le_trans hyLeM (Nat.le_add_right M x)),
                    nat_add_mod_self_left, nat_mod_eq_of_lt ha.2.2.1]
              have h5 : ∀ a b c d : Nat, (a + (b + c)) + d = (a + (d + c)) + b := by
                intro a b c d
                rw [← Nat.add_assoc a b c, Nat.add_assoc (a + b) c d, Nat.add_comm c d,
                    ← Nat.add_assoc (a + b) d c, Nat.add_assoc a b d, Nat.add_comm b d,
                    ← Nat.add_assoc a d b, Nat.add_assoc (a + d) b c, Nat.add_comm b c,
                    ← Nat.add_assoc (a + d) c b, Nat.add_assoc a d c]
              have hRe5 : (M + lo1 - hi2) + (d1 + (s2 - d2)) + y =
                  (M + lo1 - hi2) + (y + (s2 - d2)) + d1 :=
                h5 (M + lo1 - hi2) d1 (s2 - d2) y
              have hSumCandidate :
                  Nat.mod (Nat.mod (Nat.mod (M + lo1 - hi2) M +
                    (d1 + (s2 - d2))) M + y) M = x := by
                rw [mod_add_mod_left (Nat.mod (M + lo1 - hi2) M + (d1 + (s2 - d2))) y M hM,
                    Nat.add_assoc (Nat.mod (M + lo1 - hi2) M) (d1 + (s2 - d2)) y,
                    mod_add_mod_left (M + lo1 - hi2) ((d1 + (s2 - d2)) + y) M hM,
                    ← Nat.add_assoc (M + lo1 - hi2) (d1 + (s2 - d2)) y, hRe5]
                have hInner : Nat.mod ((M + lo1 - hi2) + (y + (s2 - d2))) M = lo1 := by
                  rw [← mod_add_mod_right (M + lo1 - hi2) (y + (s2 - d2)) M hM, hyMod,
                      Nat.sub_add_cancel hHi2LeM, nat_add_mod_self_left, nat_mod_eq_of_lt ha.1]
                rw [← mod_add_mod_left ((M + lo1 - hi2) + (y + (s2 - d2))) d1 M hM, hInner]
                exact hd1.2.symm
              have hCancelY : ∀ u v : Nat, u < M → v < M →
                  Nat.mod (u + y) M = Nat.mod (v + y) M → u = v := by
                intro u v hu hv hEq
                have hStep := congrArg (fun t => Nat.mod (t + (M - y)) M) hEq
                have hLHS : Nat.mod (Nat.mod (u + y) M + (M - y)) M = u := by
                  rw [mod_add_mod_left (u + y) (M - y) M hM,
                      Nat.add_assoc u y (M - y), Nat.add_comm y (M - y),
                      Nat.sub_add_cancel hyLeM, nat_add_mod_self_right, nat_mod_eq_of_lt hu]
                have hRHS : Nat.mod (Nat.mod (v + y) M + (M - y)) M = v := by
                  rw [mod_add_mod_left (v + y) (M - y) M hM,
                      Nat.add_assoc v y (M - y), Nat.add_comm y (M - y),
                      Nat.sub_add_cancel hyLeM, nat_add_mod_self_right, nat_mod_eq_of_lt hv]
                rw [hLHS, hRHS] at hStep
                exact hStep
              exact hCancelY _ _ (Nat.mod_lt _ hM) (Nat.mod_lt _ hM)
                (Eq.trans hSumTarget hSumCandidate.symm)

/-- Shorter-gap modular arc join on `WrappedInterval`. -/
@[expose] def WrappedInterval.join (M : Nat) (a b : WrappedInterval) :
    WrappedInterval :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .iv lo1 hi1, .iv lo2 hi2 =>
    match Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M with
    | false => .top
    | true =>
      let s1 := wrapSpan M lo1 hi1
      let s2 := wrapSpan M lo2 hi2
      let off12 := Nat.mod (M + lo2 - lo1) M
      let off21 := Nat.mod (M + lo1 - lo2) M
      let span1 := Nat.max s1 (off12 + s2)
      let span2 := Nat.max s2 (off21 + s1)
      match Nat.ble span1 span2 with
      | true =>
        match Nat.blt span1 (M - 1) with
        | true => .iv lo1 (Nat.mod (lo1 + span1) M)
        | false => .top
      | false =>
        match Nat.blt span2 (M - 1) with
        | true => .iv lo2 (Nat.mod (lo2 + span2) M)
        | false => .top

/-- `(b + ((M + a - b) mod M)) mod M = a mod M` for `b < M`. -/
theorem mod_add_cancel_mod (a b M : Nat) (hM : 0 < M) (hb : b < M) :
    Nat.mod (b + Nat.mod (M + a - b) M) M = Nat.mod a M := by
  have hMod : Nat.mod (b + Nat.mod (M + a - b) M) M = Nat.mod (b + (M + a - b)) M := by
    have h1 := mod_sum_mod_cancel b (M + a - b) M
    have h2 := mod_sum_mod_cancel b (Nat.mod (M + a - b) M) M
    have hIdem : Nat.mod (Nat.mod (M + a - b) M) M = Nat.mod (M + a - b) M :=
      nat_mod_eq_of_lt (Nat.mod_lt _ hM)
    rw [hIdem] at h2
    exact Eq.trans h2 h1.symm
  rw [hMod]
  have hLe : b ≤ M + a := Nat.le_trans (Nat.le_of_lt hb) (Nat.le_add_right M a)
  rw [Nat.add_comm b (M + a - b), Nat.sub_add_cancel hLe, nat_add_mod_self_left]

/-- Left upper-bound soundness of `WrappedInterval.join`. -/
theorem wrappedInterval_join_sound_left {M : Nat} (hM : 0 < M) (a b : WrappedInterval) {x : Nat}
    (ha : a.denote M x) : (WrappedInterval.join M a b).denote M x := by
  cases a with
  | bot => exact False.elim ha
  | top => cases b <;> exact ha
  | iv lo1 hi1 =>
    cases b with
    | bot => exact ha
    | top => exact ha.2.2.1
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.join]
      cases hWfCase : Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M with
      | false => exact ha.2.2.1
      | true =>
        have h123 := bool_and_true_left hWfCase
        have h12 := bool_and_true_left h123
        have hLo2Lt : lo2 < M := lt_of_blt_true (bool_and_true_right h123)
        let s1 := wrapSpan M lo1 hi1
        let s2 := wrapSpan M lo2 hi2
        let off12 := Nat.mod (M + lo2 - lo1) M
        let off21 := Nat.mod (M + lo1 - lo2) M
        let span1 := Nat.max s1 (off12 + s2)
        let span2 := Nat.max s2 (off21 + s1)
        have hxOff := (wrapped_denote_iff_offset ha.1 ha.2.1 ha.2.2.1).1 ha
        cases hxOff with
        | intro d1 hd1 =>
          cases Nat.ble span1 span2 with
          | true =>
            dsimp only
            cases hs1 : Nat.blt span1 (M - 1) with
            | false => exact ha.2.2.1
            | true =>
              dsimp only
              have hsLt : span1 < M := Nat.lt_of_lt_of_le (lt_of_blt_true hs1) (Nat.sub_le M 1)
              have hSpan := wrapped_span_of_add_lt hM ha.1 hsLt
              rw [wrapped_denote_iff_offset ha.1 hSpan.1 ha.2.2.1]
              refine ⟨d1, ?_, hd1.2⟩
              rw [hSpan.2]
              exact Nat.le_trans hd1.1 (nat_le_max_left s1 (off12 + s2))
          | false =>
            dsimp only
            cases hs2 : Nat.blt span2 (M - 1) with
            | false => exact ha.2.2.1
            | true =>
              dsimp only
              have hsLt : span2 < M := Nat.lt_of_lt_of_le (lt_of_blt_true hs2) (Nat.sub_le M 1)
              have hSpan := wrapped_span_of_add_lt hM hLo2Lt hsLt
              rw [wrapped_denote_iff_offset hLo2Lt hSpan.1 ha.2.2.1]
              refine ⟨off21 + d1, ?_, ?_⟩
              · rw [hSpan.2]
                exact Nat.le_trans (Nat.add_le_add_left hd1.1 off21)
                  (nat_le_max_right s2 (off21 + s1))
              · have hBase := mod_add_cancel_mod lo1 lo2 M hM hLo2Lt
                rw [nat_mod_eq_of_lt ha.1] at hBase
                rw [hd1.2, ← Nat.add_assoc lo2 off21 d1,
                    mod_sum_mod_cancel (lo2 + off21) d1 M, hBase]
                have hC := mod_sum_mod_cancel lo1 d1 M
                rw [nat_mod_eq_of_lt ha.1] at hC
                exact hC

/-- Right upper-bound soundness of `WrappedInterval.join`. -/
theorem wrappedInterval_join_sound_right {M : Nat} (hM : 0 < M) (a b : WrappedInterval) {x : Nat}
    (hb : b.denote M x) : (WrappedInterval.join M a b).denote M x := by
  cases a with
  | bot => exact hb
  | top => cases b <;> first | exact False.elim hb | exact hb.2.2.1 | exact hb
  | iv lo1 hi1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact hb
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.join]
      cases hWfCase : Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M with
      | false => exact hb.2.2.1
      | true =>
        have h123 := bool_and_true_left hWfCase
        have h12 := bool_and_true_left h123
        have hLo1Lt : lo1 < M := lt_of_blt_true (bool_and_true_left h12)
        have hxOff := (wrapped_denote_iff_offset hb.1 hb.2.1 hb.2.2.1).1 hb
        let s1 := wrapSpan M lo1 hi1
        let s2 := wrapSpan M lo2 hi2
        let off12 := Nat.mod (M + lo2 - lo1) M
        let off21 := Nat.mod (M + lo1 - lo2) M
        let span1 := Nat.max s1 (off12 + s2)
        let span2 := Nat.max s2 (off21 + s1)
        cases hxOff with
        | intro d2 hd2 =>
          cases Nat.ble span1 span2 with
          | true =>
            dsimp only
            cases hs1 : Nat.blt span1 (M - 1) with
            | false => exact hb.2.2.1
            | true =>
              dsimp only
              have hsLt : span1 < M := Nat.lt_of_lt_of_le (lt_of_blt_true hs1) (Nat.sub_le M 1)
              have hSpan := wrapped_span_of_add_lt hM hLo1Lt hsLt
              rw [wrapped_denote_iff_offset hLo1Lt hSpan.1 hb.2.2.1]
              refine ⟨off12 + d2, ?_, ?_⟩
              · rw [hSpan.2]
                exact Nat.le_trans (Nat.add_le_add_left hd2.1 off12)
                  (nat_le_max_right s1 (off12 + s2))
              · have hBase := mod_add_cancel_mod lo2 lo1 M hM hLo1Lt
                rw [nat_mod_eq_of_lt hb.1] at hBase
                rw [hd2.2, ← Nat.add_assoc lo1 off12 d2,
                    mod_sum_mod_cancel (lo1 + off12) d2 M, hBase]
                have hC := mod_sum_mod_cancel lo2 d2 M
                rw [nat_mod_eq_of_lt hb.1] at hC
                exact hC
          | false =>
            dsimp only
            cases hs2 : Nat.blt span2 (M - 1) with
            | false => exact hb.2.2.1
            | true =>
              dsimp only
              have hsLt : span2 < M := Nat.lt_of_lt_of_le (lt_of_blt_true hs2) (Nat.sub_le M 1)
              have hSpan := wrapped_span_of_add_lt hM hb.1 hsLt
              rw [wrapped_denote_iff_offset hb.1 hSpan.1 hb.2.2.1]
              refine ⟨d2, ?_, hd2.2⟩
              rw [hSpan.2]
              exact Nat.le_trans hd2.1 (nat_le_max_left s2 (off21 + s1))

/-- Over-approximating intersection on `WrappedInterval`. -/
@[expose] def WrappedInterval.meet (M : Nat) (a b : WrappedInterval) :
    WrappedInterval :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, x => x
  | x, .top => x
  | .iv lo1 hi1, .iv lo2 hi2 =>
    match Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M with
    | false => .bot
    | true =>
      let s1 := wrapSpan M lo1 hi1
      let s2 := wrapSpan M lo2 hi2
      let p := Nat.mod (M + lo1 - lo2) M
      match Nat.blt (p + s1) M with
      | true =>
        match Nat.blt s2 p with
        | true => .bot
        | false =>
          let u := Nat.min (p + s1) s2
          let lo' := Nat.mod (lo2 + p) M
          .iv lo' (Nat.mod (lo' + (u - p)) M)
      | false =>
        let wrapEnd := p + s1 - M
        match Nat.blt s2 p with
        | true =>
          let u := Nat.min wrapEnd s2
          .iv lo2 (Nat.mod (lo2 + u) M)
        | false =>
          match Nat.ble s1 s2 with
          | true => .iv lo1 hi1
          | false => .iv lo2 hi2

/-- Modular left-addition cancellation `(b + u) mod M = (b + v) mod M → u = v`
for `u, v < M`. -/
theorem mod_add_eq_cancel_left {M b u v : Nat} (hM : 0 < M) (hu : u < M) (hv : v < M)
    (hEq : Nat.mod (b + u) M = Nat.mod (b + v) M) : u = v := by
  have hMod : Nat.mod (b + u) M = Nat.mod (b + v) M := hEq
  have hAddInv : Nat.mod ((M - Nat.mod b M) + (b + u)) M =
      Nat.mod ((M - Nat.mod b M) + (b + v)) M := by
    rw [mod_sum_mod_cancel (M - Nat.mod b M) (b + u) M,
        mod_sum_mod_cancel (M - Nat.mod b M) (b + v) M, hMod]
  have hSimp : ∀ z : Nat, z < M → Nat.mod ((M - Nat.mod b M) + (b + z)) M = z := by
    intro z hz
    have hGen : ∀ b' q r : Nat, M * q + r = b' → r ≤ M →
        Nat.mod ((M - r) + (b' + z)) M = z := by
      intro b' q r hEqB hLe
      rw [← hEqB]
      have h1 : (M - r) + ((M * q + r) + z) = z + M * (q + 1) := by
        rw [Nat.add_assoc (M * q) r z, Nat.add_comm (M * q) (r + z),
            ← Nat.add_assoc (M - r) (r + z) (M * q),
            ← Nat.add_assoc (M - r) r z, Nat.sub_add_cancel hLe,
            Nat.add_assoc M z (M * q), Nat.add_comm M (z + M * q),
            Nat.add_assoc z (M * q) M, Nat.mul_add M q 1, Nat.mul_one]
      rw [h1, nat_add_mul_mod_self_left, nat_mod_eq_of_lt hz]
    exact hGen b (Nat.div b M) (Nat.mod b M) (nat_div_add_mod b M) (Nat.le_of_lt (Nat.mod_lt b hM))
  rw [hSimp u hu, hSimp v hv] at hAddInv
  exact hAddInv

/-- Soundness of `WrappedInterval.meet`. -/
theorem wrappedInterval_meet_sound {M : Nat} (hM : 0 < M) {a b : WrappedInterval} {x : Nat}
    (ha : a.denote M x) (hb : b.denote M x) :
    (WrappedInterval.meet M a b).denote M x := by
  cases a with
  | bot => exact False.elim ha
  | top => cases b <;> exact hb
  | iv lo1 hi1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact ha
    | iv lo2 hi2 =>
      dsimp only [WrappedInterval.meet]
      have hWf : (Nat.blt lo1 M && Nat.blt hi1 M && Nat.blt lo2 M && Nat.blt hi2 M) = true := by
        rw [blt_true_of_lt ha.1, blt_true_of_lt ha.2.1,
            blt_true_of_lt hb.1, blt_true_of_lt hb.2.1]; rfl
      rw [hWf]
      dsimp only
      let s1 := wrapSpan M lo1 hi1
      let s2 := wrapSpan M lo2 hi2
      let p := Nat.mod (M + lo1 - lo2) M
      have hpLt : p < M := Nat.mod_lt _ hM
      have hxOff1 := (wrapped_denote_iff_offset ha.1 ha.2.1 ha.2.2.1).1 ha
      have hxOff2 := (wrapped_denote_iff_offset hb.1 hb.2.1 hb.2.2.1).1 hb
      have hLo1Base := mod_add_cancel_mod lo1 lo2 M hM hb.1
      rw [nat_mod_eq_of_lt ha.1] at hLo1Base
      cases hxOff1 with
      | intro d1 hd1 =>
        cases hxOff2 with
        | intro d2 hd2 =>
          have hd2LtM : d2 < M := Nat.lt_of_le_of_lt hd2.1 (wrapSpan_lt hb.1 hb.2.1)
          have hd1LtM : d1 < M := Nat.lt_of_le_of_lt hd1.1 (wrapSpan_lt ha.1 ha.2.1)
          have hSumEq : Nat.mod (lo2 + (p + d1)) M = Nat.mod (lo2 + d2) M := by
            rw [← Nat.add_assoc lo2 p d1, mod_sum_mod_cancel (lo2 + p) d1 M, hLo1Base]
            have hC := mod_sum_mod_cancel lo1 d1 M
            rw [nat_mod_eq_of_lt ha.1] at hC
            rw [← hC, ← hd1.2, ← hd2.2]
          cases hNoWrap : Nat.blt (p + s1) M with
          | true =>
            dsimp only
            have hPsLt : p + s1 < M := lt_of_blt_true hNoWrap
            have hPd1Lt : p + d1 < M := Nat.lt_of_le_of_lt (Nat.add_le_add_left hd1.1 p) hPsLt
            have hDeq : p + d1 = d2 := mod_add_eq_cancel_left hM hPd1Lt hd2LtM hSumEq
            cases hEmpty : Nat.blt s2 p with
            | true =>
              have hS2LtP := lt_of_blt_true hEmpty
              have hBad : p ≤ s2 := by
                rw [← hDeq] at hd2
                exact Nat.le_trans (Nat.le_add_right p d1) hd2.1
              exact False.elim (Nat.not_le_of_gt hS2LtP hBad)
            | false =>
              dsimp only
              have hPs2Le : p ≤ s2 :=
                Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hEmpty; nomatch hEmpty)
              let u := Nat.min (p + s1) s2
              let lo' := Nat.mod (lo2 + p) M
              have hLo'Eq : lo' = lo1 := hLo1Base
              have huSpan : u - p ≤ s1 := by
                have hLe : u ≤ p + s1 := nat_min_le_left _ _
                have hSub : u - p ≤ (p + s1) - p := Nat.sub_le_sub_right hLe p
                rw [Nat.add_comm p s1, Nat.add_sub_cancel] at hSub
                exact hSub
              have huLtM : u - p < M := Nat.lt_of_le_of_lt huSpan (wrapSpan_lt ha.1 ha.2.1)
              have hSpan := wrapped_span_of_add_lt hM (nat_mod_lt (lo2 + p) hM) huLtM
              rw [wrapped_denote_iff_offset (nat_mod_lt (lo2 + p) hM) hSpan.1 ha.2.2.1]
              refine ⟨d1, ?_, ?_⟩
              · rw [hSpan.2]
                have hPd1LeU : p + d1 ≤ u := by
                  have h1 : p + d1 ≤ p + s1 := Nat.add_le_add_left hd1.1 p
                  have h2 : p + d1 ≤ s2 := by rw [hDeq]; exact hd2.1
                  exact nat_le_min h1 h2
                have hSub := Nat.sub_le_sub_right hPd1LeU p
                rw [Nat.add_comm p d1, Nat.add_sub_cancel] at hSub
                exact hSub
              · rw [hLo1Base, hd1.2]
          | false =>
            dsimp only
            have hGeM : M ≤ p + s1 :=
              Nat.le_of_not_lt (fun h => by rw [blt_true_of_lt h] at hNoWrap; nomatch hNoWrap)
            let wrapEnd := p + s1 - M
            have hWrapEndLt : wrapEnd < M := by
              have hSum2M : p + s1 < M + M := Nat.add_lt_add hpLt (wrapSpan_lt ha.1 ha.2.1)
              have h1 : wrapEnd + M < M + M := by rw [Nat.sub_add_cancel hGeM]; exact hSum2M
              exact nat_lt_of_add_lt_add_right h1
            cases hNoUpper : Nat.blt s2 p with
            | true =>
              dsimp only
              have hS2LtP := lt_of_blt_true hNoUpper
              have hMustWrap : M ≤ p + d1 := by
                cases Nat.lt_or_ge (p + d1) M with
                | inr hGe => exact hGe
                | inl hLt =>
                  have hDeq := mod_add_eq_cancel_left hM hLt hd2LtM hSumEq
                  have hPd2 : p ≤ s2 :=
                    Nat.le_trans (Nat.le_add_right p d1) (by rw [hDeq]; exact hd2.1)
                  exact False.elim (Nat.not_le_of_gt hS2LtP hPd2)
              have hDiffLtM : p + d1 - M < M := by
                have hSubLe : p + d1 - M ≤ p + s1 - M :=
                  Nat.sub_le_sub_right (Nat.add_le_add_left hd1.1 p) M
                exact Nat.lt_of_le_of_lt hSubLe hWrapEndLt
              have hSumWrap : Nat.mod (lo2 + (p + d1 - M)) M = Nat.mod (lo2 + d2) M := by
                have hMMod : Nat.mod (lo2 + (p + d1 - M)) M = Nat.mod (lo2 + (p + d1)) M := by
                  have hEqAdd : lo2 + (p + d1) = lo2 + (p + d1 - M) + M := by
                    rw [Nat.add_assoc lo2 (p + d1 - M) M, Nat.sub_add_cancel hMustWrap]
                  rw [hEqAdd, nat_add_mod_self_right]
                exact Eq.trans hMMod hSumEq
              have hDeqWrap := mod_add_eq_cancel_left hM hDiffLtM hd2LtM hSumWrap
              let u := Nat.min wrapEnd s2
              have huLtM : u < M := Nat.lt_of_le_of_lt (nat_min_le_left _ _) hWrapEndLt
              have hSpan := wrapped_span_of_add_lt hM hb.1 huLtM
              rw [wrapped_denote_iff_offset hb.1 hSpan.1 hb.2.2.1]
              refine ⟨d2, ?_, hd2.2⟩
              rw [hSpan.2]
              have hD2LeWrap : d2 ≤ wrapEnd := by
                rw [← hDeqWrap]; exact Nat.sub_le_sub_right (Nat.add_le_add_left hd1.1 p) M
              exact nat_le_min hD2LeWrap hd2.1
            | false =>
              dsimp only
              cases Nat.ble s1 s2 with
              | true => exact ha
              | false => exact hb

/-! ### `StridedCong` (`Nat.mod x m = r`) -/

/-- Arithmetical congruence domain: `.bot` (empty), `.top` (unconstrained
`True`), or `.cong m r` (`1 ≤ m`, `r < m`, `x mod m = r`). -/
inductive StridedCong where
  | bot
  | top
  | cong (mod rem : Nat)

/-- Well-formedness check `1 ≤ m` and `r < m` on `.cong m r`. -/
@[expose] def StridedCong.wf : StridedCong → Bool
  | .bot => true
  | .top => true
  | .cong m r => Nat.ble 1 m && Nat.blt r m

/-- Concretization of `StridedCong` on `x : Nat` (`.top` imposes no constraint).
-/
@[expose] def StridedCong.denote (c : StridedCong) (x : Nat) : Prop :=
  match c with
  | .bot => False
  | .top => True
  | .cong m r => 0 < m ∧ r < m ∧ Nat.mod x m = r

/-- Normalizing constructor `x ≡ r (mod m)` (returning `.top` when `m = 0`). -/
@[expose] def mkCong (m r : Nat) : StridedCong :=
  match Nat.beq m 0 with
  | true => .top
  | false => .cong m (Nat.mod r m)

/-- Soundness of `mkCong m r` when `0 < m` and `x mod m = r mod m`. -/
theorem mkCong_denote {m r x : Nat} (hm : 0 < m) (hMod : Nat.mod x m = Nat.mod r m) :
    (mkCong m r).denote x := by
  dsimp only [mkCong]
  cases hb : Nat.beq m 0 with
  | true => have hz := Nat.eq_of_beq_eq_true hb; rw [hz] at hm; nomatch hm
  | false => exact ⟨hm, Nat.mod_lt r hm, hMod⟩

/-- Decidable lattice order on `StridedCong` via modulus divisibility. -/
@[expose] def StridedCong.le (a b : StridedCong) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .top => true
  | .cong m1 r1, .cong m2 r2 =>
    Nat.ble 1 m1 && Nat.ble 1 m2 && Nat.blt r1 m1 && Nat.blt r2 m2 &&
      Nat.beq (Nat.mod m1 m2) 0 && Nat.beq (Nat.mod r1 m2) r2
  | _, _ => false

/-- Iterated remainder `(x mod m1) mod m2 = x mod m2` when `m2` divides `m1`. -/
theorem mod_mod_of_dvd {m1 m2 x : Nat}
    (hDvd : Nat.mod m1 m2 = 0) : Nat.mod (Nat.mod x m1) m2 = Nat.mod x m2 := by
  have hx := nat_div_add_mod x m1
  have hm := nat_div_add_mod m1 m2
  rw [hDvd, Nat.add_zero] at hm
  have hTerm : m1 * Nat.div x m1 + Nat.mod x m1 =
      (m2 * Nat.div m1 m2) * Nat.div x m1 + Nat.mod x m1 :=
    congrArg (fun z => z * Nat.div x m1 + Nat.mod x m1) hm.symm
  have hx' : x = Nat.mod x m1 + m2 * (Nat.div m1 m2 * Nat.div x m1) :=
    Eq.trans hx.symm (by rw [hTerm, Nat.mul_assoc m2 (Nat.div m1 m2) (Nat.div x m1), Nat.add_comm])
  have hMod : Nat.mod x m2 = Nat.mod (Nat.mod x m1 + m2 * (Nat.div m1 m2 * Nat.div x m1)) m2 :=
    congrArg (fun z => Nat.mod z m2) hx'
  rw [hMod, nat_add_mul_mod_self_left]

/-- Soundness of `StridedCong.le`. -/
theorem stridedCong_le_sound {a b : StridedCong} {x : Nat}
    (hLe : StridedCong.le a b = true) (ha : a.denote x) : b.denote x := by
  cases a with
  | bot => exact False.elim ha
  | top => cases b with | bot => nomatch hLe | top => exact ha | cong _ _ => nomatch hLe
  | cong m1 r1 =>
    cases b with
    | bot => nomatch hLe
    | top => exact True.intro
    | cong m2 r2 =>
      dsimp only [StridedCong.le] at hLe
      have h12345 := bool_and_true_left hLe
      have h1234 := bool_and_true_left h12345
      have h123 := bool_and_true_left h1234
      have h12 := bool_and_true_left h123
      have hm2Pos : 0 < m2 := Nat.le_of_ble_eq_true (bool_and_true_right h12)
      have hr2Lt : r2 < m2 := lt_of_blt_true (bool_and_true_right h1234)
      have hDvd : Nat.mod m1 m2 = 0 := Nat.eq_of_beq_eq_true (bool_and_true_right h12345)
      have hRem : Nat.mod r1 m2 = r2 := Nat.eq_of_beq_eq_true (bool_and_true_right hLe)
      refine ⟨hm2Pos, hr2Lt, ?_⟩
      rw [← hRem, ← ha.2.2]
      exact (mod_mod_of_dvd hDvd).symm

/-- Join on `StridedCong` preserving common modulus `8` alignment when exact
comparability fails. -/
@[expose] def StridedCong.join (a b : StridedCong) : StridedCong :=
  match a, b with
  | .bot, x => x
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .cong m1 r1, .cong m2 r2 =>
    match StridedCong.le (.cong m1 r1) (.cong m2 r2) with
    | true => .cong m2 r2
    | false =>
      match StridedCong.le (.cong m2 r2) (.cong m1 r1) with
      | true => .cong m1 r1
      | false =>
        match Nat.ble 1 m1 && Nat.ble 1 m2 && Nat.blt r1 m1 && Nat.blt r2 m2 &&
              Nat.beq (Nat.mod m1 8) 0 && Nat.beq (Nat.mod m2 8) 0 &&
              Nat.beq (Nat.mod r1 8) (Nat.mod r2 8) with
        | true => .cong 8 (Nat.mod r1 8)
        | false => .top

/-- Left upper-bound soundness of `StridedCong.join`. -/
theorem stridedCong_join_sound_left {a b : StridedCong} {x : Nat} (ha : a.denote x) :
    (StridedCong.join a b).denote x := by
  cases a with
  | bot => exact False.elim ha
  | top => cases b <;> exact True.intro
  | cong m1 r1 =>
    cases b with
    | bot => exact ha
    | top => exact True.intro
    | cong m2 r2 =>
      dsimp only [StridedCong.join]
      cases h12 : StridedCong.le (.cong m1 r1) (.cong m2 r2) with
      | true => exact stridedCong_le_sound h12 ha
      | false =>
        cases h21 : StridedCong.le (.cong m2 r2) (.cong m1 r1) with
        | true => exact ha
        | false =>
          cases h8 : Nat.ble 1 m1 && Nat.ble 1 m2 && Nat.blt r1 m1 && Nat.blt r2 m2 &&
              Nat.beq (Nat.mod m1 8) 0 && Nat.beq (Nat.mod m2 8) 0 &&
              Nat.beq (Nat.mod r1 8) (Nat.mod r2 8) with
          | false => exact True.intro
          | true =>
            have h123456 := bool_and_true_left h8
            have h12345 := bool_and_true_left h123456
            have hm1Dvd8 := Nat.eq_of_beq_eq_true (bool_and_true_right h12345)
            refine ⟨Nat.zero_lt_succ 7, Nat.mod_lt r1 (Nat.zero_lt_succ 7), ?_⟩
            rw [← ha.2.2]
            exact (mod_mod_of_dvd hm1Dvd8).symm

/-- Right upper-bound soundness of `StridedCong.join`. -/
theorem stridedCong_join_sound_right {a b : StridedCong} {x : Nat} (hb : b.denote x) :
    (StridedCong.join a b).denote x := by
  cases a with
  | bot => exact hb
  | top =>
    cases b with
    | bot => exact False.elim hb
    | top | cong _ _ => exact True.intro
  | cong m1 r1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact True.intro
    | cong m2 r2 =>
      dsimp only [StridedCong.join]
      cases h12 : StridedCong.le (.cong m1 r1) (.cong m2 r2) with
      | true => exact hb
      | false =>
        cases h21 : StridedCong.le (.cong m2 r2) (.cong m1 r1) with
        | true => exact stridedCong_le_sound h21 hb
        | false =>
          cases h8 : Nat.ble 1 m1 && Nat.ble 1 m2 && Nat.blt r1 m1 && Nat.blt r2 m2 &&
              Nat.beq (Nat.mod m1 8) 0 && Nat.beq (Nat.mod m2 8) 0 &&
              Nat.beq (Nat.mod r1 8) (Nat.mod r2 8) with
          | false => exact True.intro
          | true =>
            have h123456 := bool_and_true_left h8
            have hm2Dvd8 := Nat.eq_of_beq_eq_true (bool_and_true_right h123456)
            have hREq := Nat.eq_of_beq_eq_true (bool_and_true_right h8)
            refine ⟨Nat.zero_lt_succ 7, Nat.mod_lt r1 (Nat.zero_lt_succ 7), ?_⟩
            rw [hREq, ← hb.2.2]
            exact (mod_mod_of_dvd hm2Dvd8).symm

/-- Modular constant-addition transfer on `StridedCong` when `m` divides `M`. -/
@[expose] def StridedCong.addConst (M : Nat) (c : StridedCong) (imm : Nat) :
    StridedCong :=
  match c with
  | .bot => .bot
  | .top => .top
  | .cong m r =>
    match Nat.ble 1 m && Nat.blt r m && Nat.beq (Nat.mod M m) 0 with
    | false => .top
    | true => mkCong m (r + imm)

/-- Soundness of `StridedCong.addConst`. -/
theorem stridedCong_addConst_sound {M : Nat} {c : StridedCong} {x imm : Nat}
    (hc : c.denote x) : (StridedCong.addConst M c imm).denote (Nat.mod (x + imm) M) := by
  cases c with
  | bot => exact False.elim hc
  | top => exact True.intro
  | cong m r =>
    dsimp only [StridedCong.addConst]
    cases hCheck : Nat.ble 1 m && Nat.blt r m && Nat.beq (Nat.mod M m) 0 with
    | false => exact True.intro
    | true =>
      have hDvd := Nat.eq_of_beq_eq_true (bool_and_true_right hCheck)
      apply mkCong_denote hc.1
      rw [mod_mod_of_dvd hDvd, mod_sum_mod_cancel x imm m, hc.2.2]
      have hC := mod_sum_mod_cancel r imm m
      rw [nat_mod_eq_of_lt hc.2.1] at hC
      exact hC.symm

/-- Modular constant-subtraction transfer on `StridedCong` when `m` divides `M`.
-/
@[expose] def StridedCong.subConst (M : Nat) (c : StridedCong) (imm : Nat) :
    StridedCong :=
  match c with
  | .bot => .bot
  | .top => .top
  | .cong m r =>
    match Nat.ble 1 m && Nat.blt r m && Nat.beq (Nat.mod M m) 0 with
    | false => .top
    | true => mkCong m (r + (m - Nat.mod imm m))

/-- Soundness of `StridedCong.subConst`. -/
theorem stridedCong_subConst_sound {M : Nat} {c : StridedCong} {x imm : Nat}
    (hc : c.denote x) (hy : imm < M) :
    (StridedCong.subConst M c imm).denote (Nat.mod (M + x - imm) M) := by
  cases c with
  | bot => exact False.elim hc
  | top => exact True.intro
  | cong m r =>
    dsimp only [StridedCong.subConst]
    cases hCheck : Nat.ble 1 m && Nat.blt r m && Nat.beq (Nat.mod M m) 0 with
    | false => exact True.intro
    | true =>
      have hDvd := Nat.eq_of_beq_eq_true (bool_and_true_right hCheck)
      apply mkCong_denote hc.1
      rw [mod_mod_of_dvd hDvd]
      have hMDiv := nat_div_add_mod M m
      have hYDiv := nat_div_add_mod imm m
      rw [hDvd, Nat.add_zero] at hMDiv
      have hQyLtQm : Nat.div imm m < Nat.div M m := by
        have h1 : m * Nat.div imm m ≤ m * Nat.div imm m + Nat.mod imm m := Nat.le_add_right _ _
        rw [hYDiv] at h1
        have hLt := Nat.lt_of_le_of_lt h1 hy
        rw [← hMDiv] at hLt
        exact nat_lt_of_mul_lt_mul_left hLt
      have hQmSub : 1 ≤ Nat.div M m - Nat.div imm m := by
        have h1 : Nat.div imm m + 1 ≤ Nat.div M m := hQyLtQm
        have h2 := Nat.sub_le_sub_right h1 (Nat.div imm m)
        rw [Nat.add_comm (Nat.div imm m) 1, Nat.add_sub_cancel] at h2
        exact h2
      have hSubGen : ∀ imm' qy ry : Nat,
          m * qy + ry = imm' → ry < m → qy < Nat.div M m → 1 ≤ Nat.div M m - qy → imm' ≤ M →
          M - imm' = m * (Nat.div M m - qy - 1) + (m - ry) := by
        intro imm' qy ry hDivEq hRyLt hQyLt hSub1 hLeM'
        have hEqSum : (m * (Nat.div M m - qy - 1) + (m - ry)) + imm' = M := by
          rw [← hDivEq]
          have hStep1 : (m * (Nat.div M m - qy - 1) + (m - ry)) + (m * qy + ry) =
              m * (Nat.div M m - qy - 1 + qy) + m := by
            rw [Nat.mul_add m]
            have hRem : (m - ry) + ry = m := Nat.sub_add_cancel (Nat.le_of_lt hRyLt)
            rw [Nat.add_assoc (m * _) (m - ry),
                ← Nat.add_assoc (m - ry) (m * qy) ry,
                Nat.add_comm (m - ry) (m * qy),
                Nat.add_assoc (m * qy) (m - ry) ry,
                hRem, ← Nat.add_assoc (m * (Nat.div M m - qy - 1)) (m * qy) m]
          have hSubCancel1 : Nat.div M m - qy - 1 + 1 + qy = Nat.div M m := by
            rw [Nat.sub_add_cancel hSub1, Nat.sub_add_cancel (Nat.le_of_lt hQyLt)]
          rw [hStep1, ← Nat.mul_succ m _, Nat.succ_eq_add_one,
              Nat.add_assoc (Nat.div M m - qy - 1) qy 1,
              Nat.add_comm qy 1, ← Nat.add_assoc _ 1 _, hSubCancel1, hMDiv]
        exact (Nat.add_right_cancel (Eq.trans hEqSum (Nat.sub_add_cancel hLeM').symm)).symm
      have hSubDecomp : M - imm = m * (Nat.div M m - Nat.div imm m - 1) + (m - Nat.mod imm m) :=
        hSubGen imm (Nat.div imm m) (Nat.mod imm m) hYDiv (Nat.mod_lt imm hc.1)
          hQyLtQm hQmSub (Nat.le_of_lt hy)
      have hSubMx : M + x - imm = (M - imm) + x := by
        have hLeM : imm ≤ M := Nat.le_of_lt hy
        have h1 : (M - imm + x) + imm = M + x := by
          rw [Nat.add_assoc, Nat.add_comm x imm, ← Nat.add_assoc, Nat.sub_add_cancel hLeM]
        have h2 : (M + x - imm) + imm = M + x :=
          Nat.sub_add_cancel (Nat.le_trans hLeM (Nat.le_add_right M x))
        exact Nat.add_right_cancel (Eq.trans h2 h1.symm)
      rw [hSubMx, hSubDecomp, Nat.add_assoc (m * _) (m - Nat.mod imm m) x,
          nat_mul_add_mod_self_left, Nat.add_comm (m - Nat.mod imm m) x,
          mod_sum_mod_cancel x (m - Nat.mod imm m) m, hc.2.2]
      have hC := mod_sum_mod_cancel r (m - Nat.mod imm m) m
      rw [nat_mod_eq_of_lt hc.2.1] at hC
      exact hC.symm

/-- Meet on `StridedCong` checking comparability and mod-`8` residue
consistency. -/
@[expose] def StridedCong.meet (a b : StridedCong) : StridedCong :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, x => x
  | x, .top => x
  | .cong m1 r1, .cong m2 r2 =>
    match StridedCong.le (.cong m1 r1) (.cong m2 r2) with
    | true => .cong m1 r1
    | false =>
      match StridedCong.le (.cong m2 r2) (.cong m1 r1) with
      | true => .cong m2 r2
      | false =>
        match Nat.ble 1 m1 && Nat.ble 1 m2 &&
              Nat.beq (Nat.mod m1 8) 0 && Nat.beq (Nat.mod m2 8) 0 with
        | true =>
          match Nat.beq (Nat.mod r1 8) (Nat.mod r2 8) with
          | true => match Nat.ble m2 m1 with | true => .cong m1 r1 | false => .cong m2 r2
          | false => .bot
        | false =>
          match Nat.ble m2 m1 with
          | true => .cong m1 r1
          | false => .cong m2 r2

/-- Soundness of `StridedCong.meet`. -/
theorem stridedCong_meet_sound {a b : StridedCong} {x : Nat}
    (ha : a.denote x) (hb : b.denote x) : (StridedCong.meet a b).denote x := by
  cases a with
  | bot => exact False.elim ha
  | top => cases b <;> exact hb
  | cong m1 r1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact ha
    | cong m2 r2 =>
      dsimp only [StridedCong.meet]
      cases h12 : StridedCong.le (.cong m1 r1) (.cong m2 r2) with
      | true => exact ha
      | false =>
        cases h21 : StridedCong.le (.cong m2 r2) (.cong m1 r1) with
        | true => exact hb
        | false =>
          cases h8 : Nat.ble 1 m1 && Nat.ble 1 m2 &&
                Nat.beq (Nat.mod m1 8) 0 && Nat.beq (Nat.mod m2 8) 0 with
          | false => cases Nat.ble m2 m1 with | true => exact ha | false => exact hb
          | true =>
            have h123 := bool_and_true_left h8
            have hm1Dvd8 := Nat.eq_of_beq_eq_true (bool_and_true_right h123)
            have hm2Dvd8 := Nat.eq_of_beq_eq_true (bool_and_true_right h8)
            have hx1 : Nat.mod x 8 = Nat.mod r1 8 := by
              rw [← ha.2.2]
              exact (mod_mod_of_dvd hm1Dvd8).symm
            have hx2 : Nat.mod x 8 = Nat.mod r2 8 := by
              rw [← hb.2.2]
              exact (mod_mod_of_dvd hm2Dvd8).symm
            cases hEq : Nat.beq (Nat.mod r1 8) (Nat.mod r2 8) with
            | true => cases Nat.ble m2 m1 with | true => exact ha | false => exact hb
            | false =>
              have hR := Eq.trans hx1.symm hx2
              rw [nat_beq_of_eq hR] at hEq
              nomatch hEq

/-- General binary modular-addition transfer on `StridedCong`. -/
@[expose] def StridedCong.wrapAdd (M : Nat) (a b : StridedCong) : StridedCong :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .cong m1 r1, .cong m2 r2 =>
    match Nat.ble 1 m1 && Nat.ble 1 m2 with
    | false => .top
    | true =>
      let m :=
        match Nat.beq m1 m2 with
        | true => m1
        | false =>
          match Nat.beq (Nat.mod m1 m2) 0 with
          | true => m2
          | false =>
            match Nat.beq (Nat.mod m2 m1) 0 with
            | true => m1
            | false => 1
      match Nat.beq (Nat.mod M m) 0 && Nat.ble 2 m with
      | false => .top
      | true => mkCong m (r1 + r2)

/-- Soundness of `StridedCong.wrapAdd`. -/
theorem stridedCong_wrapAdd_sound {M : Nat} {a b : StridedCong} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) :
    (StridedCong.wrapAdd M a b).denote (Nat.mod (x + y) M) := by
  cases a with
  | bot => exact False.elim ha
  | top =>
    cases b with
    | bot => exact False.elim hb
    | top => exact True.intro
    | cong _ _ => exact True.intro
  | cong m1 r1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact True.intro
    | cong m2 r2 =>
      dsimp only [StridedCong.wrapAdd]
      have hPos12 : (Nat.ble 1 m1 && Nat.ble 1 m2) = true := by
        rw [Nat.ble_eq_true_of_le ha.1, Nat.ble_eq_true_of_le hb.1]; rfl
      rw [hPos12]
      dsimp only
      let m :=
        match Nat.beq m1 m2 with
        | true => m1
        | false =>
          match Nat.beq (Nat.mod m1 m2) 0 with
          | true => m2
          | false =>
            match Nat.beq (Nat.mod m2 m1) 0 with
            | true => m1
            | false => 1
      have hmSpec : 0 < m ∧ Nat.mod m1 m = 0 ∧ Nat.mod m2 m = 0 := by
        dsimp only [m]
        cases h12 : Nat.beq m1 m2 with
        | true =>
          have hEq := Nat.eq_of_beq_eq_true h12
          rw [hEq, nat_mod_self]; exact ⟨hb.1, rfl, rfl⟩
        | false =>
          cases hD1 : Nat.beq (Nat.mod m1 m2) 0 with
          | true => exact ⟨hb.1, Nat.eq_of_beq_eq_true hD1, nat_mod_self m2⟩
          | false =>
            cases hD2 : Nat.beq (Nat.mod m2 m1) 0 with
            | true => exact ⟨ha.1, nat_mod_self m1, Nat.eq_of_beq_eq_true hD2⟩
            | false =>
              exact ⟨Nat.zero_lt_succ 0, nat_mod_one m1, nat_mod_one m2⟩
      cases hDivM : Nat.beq (Nat.mod M m) 0 && Nat.ble 2 m with
      | false => exact True.intro
      | true =>
        have hDvdM := Nat.eq_of_beq_eq_true (bool_and_true_left hDivM)
        apply mkCong_denote hmSpec.1
        rw [mod_mod_of_dvd hDvdM, mod_sum_mod_cancel x y m]
        have hxMod : Nat.mod x m = Nat.mod r1 m := by
          rw [← ha.2.2]; exact (mod_mod_of_dvd hmSpec.2.1).symm
        have hyMod : Nat.mod y m = Nat.mod r2 m := by
          rw [← hb.2.2]; exact (mod_mod_of_dvd hmSpec.2.2).symm
        rw [hxMod, hyMod, ← mod_sum_mod_cancel r1 r2 m]

/-- General binary modular-subtraction transfer on `StridedCong`. -/
@[expose] def StridedCong.wrapSub (M : Nat) (a b : StridedCong) : StridedCong :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .cong m1 r1, .cong m2 r2 =>
    match Nat.ble 1 m1 && Nat.ble 1 m2 with
    | false => .top
    | true =>
      let m :=
        match Nat.beq m1 m2 with
        | true => m1
        | false =>
          match Nat.beq (Nat.mod m1 m2) 0 with
          | true => m2
          | false =>
            match Nat.beq (Nat.mod m2 m1) 0 with
            | true => m1
            | false => 1
      match Nat.beq (Nat.mod M m) 0 && Nat.ble 2 m with
      | false => .top
      | true => mkCong m (r1 + (m - Nat.mod r2 m))

/-- Soundness of `StridedCong.wrapSub`. -/
theorem stridedCong_wrapSub_sound {M : Nat} {a b : StridedCong} {x y : Nat}
    (ha : a.denote x) (hb : b.denote y) (hy : y < M) :
    (StridedCong.wrapSub M a b).denote (Nat.mod (M + x - y) M) := by
  cases a with
  | bot => exact False.elim ha
  | top =>
    cases b with
    | bot => exact False.elim hb
    | top => exact True.intro
    | cong _ _ => exact True.intro
  | cong m1 r1 =>
    cases b with
    | bot => exact False.elim hb
    | top => exact True.intro
    | cong m2 r2 =>
      dsimp only [StridedCong.wrapSub]
      have hPos12 : (Nat.ble 1 m1 && Nat.ble 1 m2) = true := by
        rw [Nat.ble_eq_true_of_le ha.1, Nat.ble_eq_true_of_le hb.1]; rfl
      rw [hPos12]
      dsimp only
      let m :=
        match Nat.beq m1 m2 with
        | true => m1
        | false =>
          match Nat.beq (Nat.mod m1 m2) 0 with
          | true => m2
          | false =>
            match Nat.beq (Nat.mod m2 m1) 0 with
            | true => m1
            | false => 1
      have hmSpec : 0 < m ∧ Nat.mod m1 m = 0 ∧ Nat.mod m2 m = 0 := by
        dsimp only [m]
        cases h12 : Nat.beq m1 m2 with
        | true =>
          have hEq := Nat.eq_of_beq_eq_true h12
          rw [hEq, nat_mod_self]; exact ⟨hb.1, rfl, rfl⟩
        | false =>
          cases hD1 : Nat.beq (Nat.mod m1 m2) 0 with
          | true => exact ⟨hb.1, Nat.eq_of_beq_eq_true hD1, nat_mod_self m2⟩
          | false =>
            cases hD2 : Nat.beq (Nat.mod m2 m1) 0 with
            | true => exact ⟨ha.1, nat_mod_self m1, Nat.eq_of_beq_eq_true hD2⟩
            | false => exact ⟨Nat.zero_lt_succ 0, nat_mod_one m1, nat_mod_one m2⟩
      cases hDivM : Nat.beq (Nat.mod M m) 0 && Nat.ble 2 m with
      | false => exact True.intro
      | true =>
        have hDvdM := Nat.eq_of_beq_eq_true (bool_and_true_left hDivM)
        have hXRed : StridedCong.denote (.cong m (Nat.mod r1 m)) x :=
          ⟨hmSpec.1, nat_mod_lt r1 hmSpec.1,
            by rw [← ha.2.2]; exact (mod_mod_of_dvd hmSpec.2.1).symm⟩
        have hyModEq : Nat.mod y m = Nat.mod r2 m := by
          rw [← hb.2.2]; exact (mod_mod_of_dvd hmSpec.2.2).symm
        let cSub := StridedCong.subConst M (.cong m (Nat.mod r1 m)) y
        have hWfCheck :
            (Nat.ble 1 m && Nat.blt (Nat.mod r1 m) m && Nat.beq (Nat.mod M m) 0) = true := by
          rw [Nat.ble_eq_true_of_le hmSpec.1,
              blt_true_of_lt (nat_mod_lt r1 hmSpec.1), nat_beq_of_eq hDvdM]; rfl
        have hSub := stridedCong_subConst_sound hXRed hy
        dsimp only [StridedCong.subConst] at hSub
        rw [hWfCheck] at hSub
        dsimp only at hSub
        have hSame : mkCong m (Nat.mod r1 m + (m - Nat.mod y m)) =
            mkCong m (r1 + (m - Nat.mod r2 m)) := by
          dsimp only [mkCong]
          cases hm0 : Nat.beq m 0 with
          | true => rfl
          | false =>
            have hModEq : Nat.mod (Nat.mod r1 m + (m - Nat.mod y m)) m =
                          Nat.mod (r1 + (m - Nat.mod r2 m)) m := by
              rw [← hyModEq]
              have hIdem : Nat.mod (Nat.mod r1 m) m = Nat.mod r1 m :=
                nat_mod_eq_of_lt (nat_mod_lt r1 hmSpec.1)
              have hL := mod_sum_mod_cancel (Nat.mod r1 m) (m - Nat.mod y m) m
              have hR := mod_sum_mod_cancel r1 (m - Nat.mod y m) m
              rw [hIdem] at hL
              exact Eq.trans hL hR.symm
            rw [hModEq]
        rw [← hSame]
        exact hSub

end Anneal.AiPcc

end
