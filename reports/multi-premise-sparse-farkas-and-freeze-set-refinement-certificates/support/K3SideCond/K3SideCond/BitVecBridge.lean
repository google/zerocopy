-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import K3SideCond.SparseFarkas

/-!
# Modular `BitVec w` to Mathematical `Int` No-Wrap Bridge for `FarkasCertN` (`BitVecBridge.lean`)

Bridges fixed-width modular machine arithmetic (`BitVec w` with unsigned `nuw` or signed `nsw`
interval bounds from `BitDomainCert`) to the mathematical integer inequalities (`Int`) consumed
by `FarkasCertN`.
Specifically, proves that when `0 ≤ x`, `0 ≤ y`, `0 ≤ stride`, and `x * stride + y < 2^w`
(witnessed by `IntervalNoWrapCert`), the modular `UInt64`/`BitVec w` affine index expression
`(x * stride + y) % 2^w` equals the mathematical integer `x * stride + y`, allowing
`checkFarkasCertN` to discharge slice bounds checks (`idx < len`) soundly.
-/

namespace K3SideCond

/-- Interval bound `[lo, hi]` for a register or affine subexpression, paired with a modulus `modPow2`
($2^w$ for unsigned `nuw`, or $2^{w-1}$ for signed `nsw`). -/
structure IntervalNoWrapCert where
  loA      : Int
  hiA      : Int
  loB      : Int
  hiB      : Int
  stride   : Int
  modLimit : Int
  deriving DecidableEq, Repr

/-- Executable checker verifying that for all `a ∈ [loA, hiA]` and `b ∈ [loB, hiB]`,
the affine index `a * stride + b` lies strictly inside `[0, modLimit)` and therefore never
wraps modulo `modLimit`. -/
def checkIntervalNoWrap (c : IntervalNoWrapCert) : Bool :=
  decide (0 ≤ c.loA ∧ c.loA ≤ c.hiA ∧
          0 ≤ c.loB ∧ c.loB ≤ c.hiB ∧
          0 ≤ c.stride ∧
          c.hiA * c.stride + c.hiB < c.modLimit)

/-- Soundness of `checkIntervalNoWrap`: any `(a, b)` within `[loA, hiA] × [loB, hiB]`
satisfies `0 ≤ a * stride + b < modLimit`, so `(a * stride + b) % modLimit = a * stride + b`. -/
theorem checkIntervalNoWrap_sound (c : IntervalNoWrapCert)
    (h_ok : checkIntervalNoWrap c = true)
    (a b : Int)
    (ha_lo : c.loA ≤ a) (ha_hi : a ≤ c.hiA)
    (hb_lo : c.loB ≤ b) (hb_hi : b ≤ c.hiB) :
    0 ≤ a * c.stride + b ∧ a * c.stride + b < c.modLimit ∧
    (a * c.stride + b) % c.modLimit = a * c.stride + b := by
  unfold checkIntervalNoWrap at h_ok
  simp only [decide_eq_true_eq] at h_ok
  rcases h_ok with ⟨h_loA0, _, h_loB0, _, h_str0, h_top⟩
  have ha0 : 0 ≤ a := Int.le_trans h_loA0 ha_lo
  have hb0 : 0 ≤ b := Int.le_trans h_loB0 hb_lo
  have h_mul_lo : 0 ≤ a * c.stride := Int.mul_nonneg ha0 h_str0
  have h_mul_hi : a * c.stride ≤ c.hiA * c.stride :=
    Int.mul_le_mul_of_nonneg_right ha_hi h_str0
  have h_nonneg : 0 ≤ a * c.stride + b := by omega
  have h_lt : a * c.stride + b < c.modLimit := by omega
  refine ⟨h_nonneg, h_lt, ?_⟩
  exact Int.emod_eq_of_lt h_nonneg h_lt

/-- Combined `BitVec`-to-`Int` bridged Farkas certificate: pairs an `IntervalNoWrapCert`
justifying absence of modular wraparound with a multi-premise `FarkasCertN` proving the
target bounds obligation. -/
structure BridgedFarkasCert where
  noWrap : IntervalNoWrapCert
  farkas : FarkasCertN
  deriving DecidableEq, Repr

def checkBridgedFarkasCert (cert : BridgedFarkasCert) : Bool :=
  checkIntervalNoWrap cert.noWrap && checkFarkasCertN cert.farkas

theorem checkBridgedFarkasCert_sound (cert : BridgedFarkasCert)
    (h_check : checkBridgedFarkasCert cert = true)
    (env : Nat → Int)
    (ha_lo : cert.noWrap.loA ≤ env 0) (ha_hi : env 0 ≤ cert.noWrap.hiA)
    (hb_lo : cert.noWrap.loB ≤ env 1) (hb_hi : env 1 ≤ cert.noWrap.hiB)
    (h_holds : AllPremisesHold env cert.farkas.premises) :
    (env 0 * cert.noWrap.stride + env 1) % cert.noWrap.modLimit =
      env 0 * cert.noWrap.stride + env 1 ∧
    ¬ cert.farkas.negTarget.holds env := by
  unfold checkBridgedFarkasCert at h_check
  simp only [Bool.and_eq_true] at h_check
  have h_nw := checkIntervalNoWrap_sound cert.noWrap h_check.1 (env 0) (env 1) ha_lo ha_hi hb_lo hb_hi
  have h_fk := checkFarkasCertN_sound cert.farkas h_check.2 env h_holds
  exact ⟨h_nw.2.2, h_fk⟩

end K3SideCond
