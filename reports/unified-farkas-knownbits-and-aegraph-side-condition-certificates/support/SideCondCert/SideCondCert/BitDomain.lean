-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import SideCondCert.Domain

namespace SideCondCert

/-- Abstract `KnownBits` domain `(zeroMask, oneMask)` over 64-bit `UInt64` words
(matching LLVM `llvm::KnownBits` in `llvm/Support/KnownBits.h`):
- `zeroMask`: bit positions guaranteed to be `0` (`(v &&& zeroMask) == 0`);
- `oneMask`:  bit positions guaranteed to be `1` (`(v &&& oneMask) == oneMask`). -/
structure KnownBits64 where
  zeroMask : UInt64
  oneMask  : UInt64
  deriving DecidableEq, Repr

/-- Well-formedness: no bit can be simultaneously known `0` and known `1`. -/
def KnownBits64.isConsistent (kb : KnownBits64) : Bool :=
  decide ((kb.zeroMask &&& kb.oneMask) = 0)

/-- Concrete membership predicate `v ∈ γ(kb)`. -/
def KnownBits64.matchesVal (kb : KnownBits64) (v : UInt64) : Prop :=
  (v &&& kb.zeroMask) = 0 ∧ (v &&& kb.oneMask) = kb.oneMask

/-- Forward abstract transfer function for bitwise `AND` (`KnownBits::blsi` / `operator&`):
- A bit is known `0` in `a &&& b` if it is known `0` in `a` OR known `0` in `b`;
- A bit is known `1` in `a &&& b` if it is known `1` in `a` AND known `1` in `b`. -/
def KnownBits64.transferAnd (ka kb : KnownBits64) : KnownBits64 :=
  { zeroMask := ka.zeroMask ||| kb.zeroMask
    oneMask  := ka.oneMask  &&& kb.oneMask }

/-- Forward abstract transfer function for bitwise `OR` (`KnownBits::operator|`):
- A bit is known `0` in `a ||| b` if it is known `0` in `a` AND known `0` in `b`;
- A bit is known `1` in `a ||| b` if it is known `1` in `a` OR known `1` in `b`. -/
def KnownBits64.transferOr (ka kb : KnownBits64) : KnownBits64 :=
  { zeroMask := ka.zeroMask &&& kb.zeroMask
    oneMask  := ka.oneMask  ||| kb.oneMask }

/-- Forward abstract transfer function for bitwise `XOR` (`KnownBits::operator^`). -/
def KnownBits64.transferXor (ka kb : KnownBits64) : KnownBits64 :=
  { zeroMask := (ka.zeroMask &&& kb.zeroMask) ||| (ka.oneMask &&& kb.oneMask)
    oneMask  := (ka.zeroMask &&& kb.oneMask)  ||| (ka.oneMask &&& kb.zeroMask) }

/-- Unsigned interval `[lo, hi]` with modulus `modulus` for `nuw`/`nsw` range certificates. -/
structure IntervalCert where
  lo1     : Nat
  hi1     : Nat
  lo2     : Nat
  hi2     : Nat
  modulus : Nat
  deriving DecidableEq, Repr

/-- Certificate variants for `BitDomainCert` (`KnownBits` + `ConstantRange` side conditions). -/
inductive BitDomainCert where
  /-- Certifies that two bitmasks `m1, m2` have no overlapping possible `1`-bits
      (`(~zeroMask1) &&& (~zeroMask2) == 0`), discharging `disjoint_or` (`a + b -> a | b`)
      and `a & b -> 0` in `InstCombine`. -/
  | disjointMasks (z1 o1 z2 o2 : UInt64)
  /-- Certifies that an expression with `KnownBits (z, o)` is guaranteed non-zero (`o != 0`). -/
  | knownNonZero (z o : UInt64)
  /-- Certifies that `x + y` cannot overflow `[0, modulus)` given `x ∈ [lo1, hi1]` and
      `y ∈ [lo2, hi2]` (`hi1 + hi2 < modulus`), discharging `add nuw` introduction/elimination. -/
  | addNoUnsignedWrap (iv : IntervalCert)
  /-- Certifies that `(x & mask) < bound` because `mask < bound` (`SelectionDAG` demanded bits). -/
  | maskUpperBound (mask bound : Nat)
  deriving DecidableEq, Repr

/-- Executable $O(1)$ checker for `BitDomainCert`. -/
def checkBitDomainCert : BitDomainCert → Bool
  | .disjointMasks z1 o1 z2 o2 =>
      decide ((z1 &&& o1) = 0 ∧ (z2 &&& o2) = 0 ∧ ((~~~z1) &&& (~~~z2)) = 0)
  | .knownNonZero z o =>
      decide ((z &&& o) = 0 ∧ o ≠ 0)
  | .addNoUnsignedWrap iv =>
      decide (iv.lo1 ≤ iv.hi1 ∧ iv.lo2 ≤ iv.hi2 ∧ iv.hi1 + iv.hi2 < iv.modulus)
  | .maskUpperBound mask bound =>
      decide (mask < bound)

/-- Declarative validity specification for `BitDomainCert`. -/
inductive ValidBitDomainCert : BitDomainCert → Prop where
  | disjointMasks (z1 o1 z2 o2 : UInt64)
      (hc1 : (z1 &&& o1) = 0) (hc2 : (z2 &&& o2) = 0)
      (hdisj : ((~~~z1) &&& (~~~z2)) = 0) :
      ValidBitDomainCert (.disjointMasks z1 o1 z2 o2)
  | knownNonZero (z o : UInt64)
      (hc : (z &&& o) = 0) (hnz : o ≠ 0) :
      ValidBitDomainCert (.knownNonZero z o)
  | addNoUnsignedWrap (iv : IntervalCert)
      (h1 : iv.lo1 ≤ iv.hi1) (h2 : iv.lo2 ≤ iv.hi2) (hsum : iv.hi1 + iv.hi2 < iv.modulus) :
      ValidBitDomainCert (.addNoUnsignedWrap iv)
  | maskUpperBound (mask bound : Nat) (hlt : mask < bound) :
      ValidBitDomainCert (.maskUpperBound mask bound)

/-- Soundness of `addNoUnsignedWrap`: whenever `checkBitDomainCert (.addNoUnsignedWrap iv) = true`,
any `x ∈ [iv.lo1, iv.hi1]` and `y ∈ [iv.lo2, iv.hi2]` satisfy `x + y < iv.modulus`
(no unsigned wraparound occurs). -/
theorem checkBitDomain_addNuw_sound (iv : IntervalCert)
    (h_check : checkBitDomainCert (.addNoUnsignedWrap iv) = true)
    (x y : Nat)
    (_hx_lo : iv.lo1 ≤ x) (hx_hi : x ≤ iv.hi1)
    (_hy_lo : iv.lo2 ≤ y) (hy_hi : y ≤ iv.hi2) :
    x + y < iv.modulus := by
  simp only [checkBitDomainCert, decide_eq_true_eq] at h_check
  omega

/-- Soundness of `knownNonZero`: whenever `checkBitDomainCert (.knownNonZero z o) = true`
and `v` matches `KnownBits64 (z, o)`, `v ≠ 0`. -/
theorem checkBitDomain_knownNonZero_sound (z o v : UInt64)
    (h_check : checkBitDomainCert (.knownNonZero z o) = true)
    (h_match : (KnownBits64.mk z o).matchesVal v) :
    v ≠ 0 := by
  simp only [checkBitDomainCert, decide_eq_true_eq] at h_check
  rcases h_check with ⟨_, h_nz⟩
  rcases h_match with ⟨_, h_one⟩
  intro h_v0
  subst h_v0
  have h_zero_and : ((0 : UInt64) &&& o) = 0 := by
    apply UInt64.eq_of_toBitVec_eq
    simp
  rw [h_zero_and] at h_one
  exact h_nz h_one.symm

/-- Bidirectional equivalence between `checkBitDomainCert` and `ValidBitDomainCert`. -/
theorem checkBitDomainCert_iff_valid (c : BitDomainCert) :
    checkBitDomainCert c = true ↔ ValidBitDomainCert c := by
  constructor
  · intro h
    cases c with
    | disjointMasks z1 o1 z2 o2 =>
      simp only [checkBitDomainCert, decide_eq_true_eq] at h
      exact .disjointMasks z1 o1 z2 o2 h.1 h.2.1 h.2.2
    | knownNonZero z o =>
      simp only [checkBitDomainCert, decide_eq_true_eq] at h
      exact .knownNonZero z o h.1 h.2
    | addNoUnsignedWrap iv =>
      simp only [checkBitDomainCert, decide_eq_true_eq] at h
      exact .addNoUnsignedWrap iv h.1 h.2.1 h.2.2
    | maskUpperBound m b =>
      simp only [checkBitDomainCert, decide_eq_true_eq] at h
      exact .maskUpperBound m b h
  · intro h
    cases h with
    | disjointMasks _ _ _ _ h1 h2 h3 => simp [checkBitDomainCert, h1, h2, h3]
    | knownNonZero _ _ h1 h2 => simp [checkBitDomainCert, h1, h2]
    | addNoUnsignedWrap _ h1 h2 h3 => simp [checkBitDomainCert, h1, h2, h3]
    | maskUpperBound _ _ h1 => simp [checkBitDomainCert, h1]

end SideCondCert
