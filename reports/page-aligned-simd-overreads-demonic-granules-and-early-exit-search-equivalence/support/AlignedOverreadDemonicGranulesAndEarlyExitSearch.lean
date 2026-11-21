-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic

/-!
Pass-1 Lean 4 (`v4.34.1`) mechanization of:
1. Power-of-two hardware protection granules (`granuleBits`: `12` for 4 KiB MMU
   pages without MTE, `4` for 16-byte AArch64 MTE tag granules, `0` for strict
   byte-exact / MMIO regimes) and aligned over-read containment;
2. `DemonicGranuleLoad` semantics, demonic slack obliviousness characterization
   of `TotalMirAsmDemonicEquiv`, off-by-one mask refutation, and 1-safety vs.
   2-safety `LeakTrace` split for unmasked fast-path branches;
3. Bitmask windowing (`packBits`, `shrxMask`, `bzhiMask`), `CpuFeatures.bmi1`
   `tzcnt` vs. `bsf` zero-input hazard, variable-stride early-exit simulation,
   and full end-to-end `early_exit_simd_search_equiv` (empty guard -> misaligned
   masked prolog -> aligned main loop -> masked epilog).

Conforms strictly to Anneal Pass-1 syntax rules: `prelude` + locked `Init.*`
imports only; zero `sorry`, zero custom `axiom`, zero `._unsafe_rec`, zero
`omega`/`bv_decide`/`native_decide`, and zero banned operator notations.
-/

namespace AlignedSimdOverread

-- ============================================================================
-- 1. Power-of-Two Granules and Aligned Span Containment
-- ============================================================================

/-- `2^k` defined via `Nat.rec` to guarantee zero `._unsafe_rec` auxiliaries. -/
def pow2 (k : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ acc => 2 * acc) k

theorem pow2_zero : pow2 0 = 1 := rfl

theorem pow2_succ (k : Nat) : pow2 (k + 1) = 2 * pow2 k := rfl

theorem pow2_pos (k : Nat) : 0 < pow2 k := by
  induction k with
  | zero => exact Nat.zero_lt_succ 0
  | succ n ih =>
    rw [pow2_succ]
    have h2 : 2 * pow2 n = pow2 n + pow2 n := Nat.two_mul (pow2 n)
    rw [h2]
    exact Nat.add_lt_add ih ih

theorem pow2_add (a b : Nat) : pow2 (a + b) = pow2 b * pow2 a := by
  induction b with
  | zero =>
    rw [Nat.add_zero, pow2_zero, Nat.one_mul]
  | succ n ih =>
    rw [Nat.add_succ, pow2_succ, pow2_succ, ih, Nat.mul_assoc]

/-- Align `addr` down to a multiple of `2^k`: `(addr / 2^k) * 2^k`. -/
def alignDown (k addr : Nat) : Nat :=
  Nat.div addr (pow2 k) * pow2 k

theorem alignDown_zero (addr : Nat) : alignDown 0 addr = addr := by
  dsimp [alignDown]
  rw [pow2_zero]
  have hd : Nat.div addr 1 = addr := Nat.div_one addr
  rw [hd, Nat.mul_one]

theorem alignDown_mod_eq_zero (k addr : Nat) :
    Nat.mod (alignDown k addr) (pow2 k) = 0 :=
  Nat.mul_mod_left (Nat.div addr (pow2 k)) (pow2 k)

/-- Theorem 1: Every address `addr` lies inside `[alignDown k addr, alignDown k addr + 2^k)`. -/
theorem alignDown_bounds (k addr : Nat) :
    alignDown k addr ≤ addr ∧ addr < alignDown k addr + pow2 k := by
  apply And.intro
  · exact Nat.div_mul_le_self addr (pow2 k)
  · have hdiv : pow2 k * Nat.div addr (pow2 k) + Nat.mod addr (pow2 k) = addr :=
      Nat.div_add_mod addr (pow2 k)
    have hlt : Nat.mod addr (pow2 k) < pow2 k :=
      Nat.mod_lt addr (pow2_pos k)
    have hcomm : pow2 k * Nat.div addr (pow2 k) = alignDown k addr :=
      Nat.mul_comm (pow2 k) (Nat.div addr (pow2 k))
    have hdiv' : alignDown k addr + Nat.mod addr (pow2 k) = addr := by
      rw [← hcomm]
      exact hdiv
    have hsum : alignDown k addr + Nat.mod addr (pow2 k) < alignDown k addr + pow2 k :=
      Nat.add_lt_add_left hlt (alignDown k addr)
    rw [hdiv'] at hsum
    exact hsum

/-- Theorem 2 (Granule Containment Law): Whenever `k ≤ granuleBits` (`2^k ≤ 2^granuleBits`),
    the `2^k`-aligned span around `addr` stays completely inside `addr`'s `2^granuleBits`
    hardware protection granule `[alignDown granuleBits addr, alignDown granuleBits addr + 2^granuleBits)`. -/
theorem aligned_load_stays_in_granule (k granuleBits addr : Nat)
    (hkle : k ≤ granuleBits) :
    alignDown granuleBits addr ≤ alignDown k addr ∧
    alignDown k addr + pow2 k ≤ alignDown granuleBits addr + pow2 granuleBits := by
  have hsplit : k + (granuleBits - k) = granuleBits := Nat.add_sub_of_le hkle
  let d := granuleBits - k
  have hg : granuleBits = k + d := Eq.symm hsplit
  rw [hg]
  have hpow : pow2 (k + d) = pow2 d * pow2 k := pow2_add k d
  have hpow2 : pow2 (k + d) = pow2 k * pow2 d := by
    rw [hpow]
    exact Nat.mul_comm (pow2 d) (pow2 k)
  let q := Nat.div addr (pow2 k)
  have hdivG : Nat.div addr (pow2 (k + d)) = Nat.div q (pow2 d) := by
    rw [hpow2]
    exact Eq.symm (Nat.div_div_eq_div_mul addr (pow2 k) (pow2 d))
  have halgnG : alignDown (k + d) addr = (Nat.div q (pow2 d) * pow2 d) * pow2 k := by
    dsimp [alignDown]
    rw [hdivG, hpow, Nat.mul_assoc]
  apply And.intro
  · rw [halgnG]
    dsimp [alignDown]
    exact Nat.mul_le_mul_right (pow2 k) (Nat.div_mul_le_self q (pow2 d))
  · rw [halgnG, hpow]
    have hq_lt : q < Nat.div q (pow2 d) * pow2 d + pow2 d := by
      have hdm : pow2 d * Nat.div q (pow2 d) + Nat.mod q (pow2 d) = q :=
        Nat.div_add_mod q (pow2 d)
      have hmlt : Nat.mod q (pow2 d) < pow2 d := Nat.mod_lt q (pow2_pos d)
      have hc : pow2 d * Nat.div q (pow2 d) = Nat.div q (pow2 d) * pow2 d :=
        Nat.mul_comm (pow2 d) (Nat.div q (pow2 d))
      have hdm' : Nat.div q (pow2 d) * pow2 d + Nat.mod q (pow2 d) = q := by
        rw [← hc]
        exact hdm
      have hs : Nat.div q (pow2 d) * pow2 d + Nat.mod q (pow2 d) <
          Nat.div q (pow2 d) * pow2 d + pow2 d :=
        Nat.add_lt_add_left hmlt (Nat.div q (pow2 d) * pow2 d)
      rw [hdm'] at hs
      exact hs
    have hq_le : q + 1 ≤ Nat.div q (pow2 d) * pow2 d + pow2 d := hq_lt
    have hmul : (q + 1) * pow2 k ≤ (Nat.div q (pow2 d) * pow2 d + pow2 d) * pow2 k :=
      Nat.mul_le_mul_right (pow2 k) hq_le
    have hlhs : (q + 1) * pow2 k = alignDown k addr + pow2 k := by
      rw [Nat.add_mul, Nat.one_mul]
      rfl
    have hrhs : (Nat.div q (pow2 d) * pow2 d + pow2 d) * pow2 k =
        (Nat.div q (pow2 d) * pow2 d) * pow2 k + pow2 d * pow2 k :=
      Nat.add_mul (Nat.div q (pow2 d) * pow2 d) (pow2 d) (pow2 k)
    rw [← hlhs, ← hrhs]
    exact hmul

-- ============================================================================
-- 2. Granule-Parameterized `DemonicGranuleLoad` & Boundary Specializations
-- ============================================================================

/-- Propositional admissibility predicate for an aligned `2^k`-byte non-volatile load
    under hardware protection granule `2^granuleBits`:
    1. Load width does not exceed the protection granule (`k ≤ granuleBits`);
    2. `alignedAddr` is `2^k`-aligned;
    3. `[alignedAddr, alignedAddr + 2^k)` contains at least one live readable byte `b`
       inside the authorized slice `[authBase, authBase + authLen)`. -/
def GranuleLoadAdmissible
    (granuleBits authBase authLen k alignedAddr : Nat) : Prop :=
  k ≤ granuleBits ∧
  Nat.mod alignedAddr (pow2 k) = 0 ∧
  ∃ b, alignedAddr ≤ b ∧ b < alignedAddr + pow2 k ∧
       authBase ≤ b ∧ b < authBase + authLen

/-- Corollary 3 (`len == 1` Invariance): For any single-byte (or non-empty) slice at `ptr`
    (`1 ≤ len`) and `k ≤ granuleBits`, `alignDown k ptr` is strictly admissible and stays
    inside `ptr`'s `2^granuleBits` granule at every intra-granule offset. -/
theorem single_byte_slice_admissible_and_contained
    (granuleBits ptr len k : Nat) (hkle : k ≤ granuleBits) (hlen : 1 ≤ len) :
    GranuleLoadAdmissible granuleBits ptr len k (alignDown k ptr) ∧
    alignDown granuleBits ptr ≤ alignDown k ptr ∧
    alignDown k ptr + pow2 k ≤ alignDown granuleBits ptr + pow2 granuleBits := by
  have hb := alignDown_bounds k ptr
  have hp_lt : ptr < ptr + len := by
    have h1 : ptr + 0 < ptr + len := Nat.add_lt_add_left hlen ptr
    rw [Nat.add_zero] at h1
    exact h1
  exact And.intro
    (And.intro hkle
      (And.intro (alignDown_mod_eq_zero k ptr)
        (Exists.intro ptr (And.intro hb.1 (And.intro hb.2 (And.intro (Nat.le_refl ptr) hp_lt))))))
    (aligned_load_stays_in_granule k granuleBits ptr hkle)

/-- Theorem 4 (`granuleBits = 0` Strict In-Bounds Recovery):
    Setting `granuleBits = 0` (MMIO / strict byte-exact regime) collapses
    `GranuleLoadAdmissible` to `k = 0` (`1`-byte load) with `alignedAddr` strictly
    in `[authBase, authBase + authLen)`. -/
theorem demonicGranuleLoad_zero_recovers_strict_inbounds
    (authBase authLen k alignedAddr : Nat) :
    GranuleLoadAdmissible 0 authBase authLen k alignedAddr ↔
      (k = 0 ∧ authBase ≤ alignedAddr ∧ alignedAddr < authBase + authLen) := by
  apply Iff.intro
  · intro h
    cases h with
    | intro hk hrest =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      cases hrest with
      | intro _ hex =>
        cases hex with
        | intro b hb =>
          have h1 : alignedAddr ≤ b := hb.1
          have h2 : b < alignedAddr + 1 := hb.2.1
          have hbe : b = alignedAddr := Nat.le_antisymm (Nat.le_of_lt_succ h2) h1
          subst hbe
          exact And.intro rfl (And.intro hb.2.2.1 hb.2.2.2)
  · intro h
    have hk0 : k = 0 := h.1
    subst hk0
    have hm1 : Nat.mod alignedAddr (pow2 0) = 0 := by
      rw [pow2_zero]
      exact Nat.mod_one alignedAddr
    have hlt1 : alignedAddr < alignedAddr + pow2 0 := by
      rw [pow2_zero]
      exact Nat.lt_succ_self alignedAddr
    exact And.intro (Nat.le_refl 0)
      (And.intro hm1
        (Exists.intro alignedAddr
          (And.intro (Nat.le_refl alignedAddr)
            (And.intro hlt1 (And.intro h.2.1 h.2.2)))))

/-- Theorem 5 (`len == 0` Trap): An empty slice (`authLen = 0`) admits NO granule load
    at any address—covering both `NonNull::dangling() = 0x1` (`alignDown 5 1 = 0`) and
    valid page-end empty slices `&page[4096..4096]` (`alignDown 5 4096 = 4096`). -/
theorem empty_slice_unguarded_not_admissible
    (granuleBits authBase k alignedAddr : Nat) :
    ¬ GranuleLoadAdmissible granuleBits authBase 0 k alignedAddr := by
  intro h
  cases h with
  | intro _ hrest =>
    cases hrest with
    | intro _ hex =>
      cases hex with
      | intro b hb =>
        have hlo : authBase ≤ b := hb.2.2.1
        have hhi : b < authBase + 0 := hb.2.2.2
        rw [Nat.add_zero] at hhi
        exact Nat.not_lt_of_ge hlo hhi

/-- Theorem 6 (`G_arch = 16 < loadSize = 32` AArch64 MTE Fault Witness):
    Under 16-byte AArch64 MTE granules (`granuleBits = 4`), 32-byte aligned loads (`k = 5`)
    are rejected by `GranuleLoadAdmissible`, and align-down at both `[0, 8)` (granule 0)
    and `[16, 24)` (granule 1) accesses addresses in a mismatched 16-byte MTE tag granule. -/
theorem mte_16b_granule_rejects_32b_load_and_crosses_tag
    (authBase authLen alignedAddr : Nat) :
    ¬ GranuleLoadAdmissible 4 authBase authLen 5 alignedAddr ∧
    (alignDown 5 0 = 0 ∧ alignDown 4 0 = 0 ∧ alignDown 4 16 = 16) ∧
    (alignDown 5 16 = 0 ∧ alignDown 4 16 = 16 ∧ alignDown 4 0 = 0) := by
  apply And.intro
  · intro h
    have hk : 5 ≤ 4 := h.1
    have hnot : ¬ (5 ≤ 4) := by decide
    exact hnot hk
  · exact And.intro (And.intro rfl (And.intro rfl rfl)) (And.intro rfl (And.intro rfl rfl))

-- ============================================================================
-- 3. Demonic Slack Obliviousness, Off-by-One Refutation, & 2-Safety `LeakTrace`
-- ============================================================================

def inSlice (authBase authLen addr : Nat) : Bool :=
  Nat.ble authBase addr && Nat.blt addr (authBase + authLen)

/-- Per-load demonic lane read: returns the exact authorized memory byte inside
    `[authBase, authBase + authLen)`, and a fresh demonic byte `demonStep lane`
    outside the authorized slice (stripping provenance and modeling uninit padding,
    unexposed sibling allocations, and concurrent neighbor writes). -/
def demonicReadLane
    (authBase authLen : Nat) (mem : Nat → Nat) (demonStep : Nat → Nat)
    (alignedAddr lane : Nat) : Nat :=
  match inSlice authBase authLen (alignedAddr + lane) with
  | true => mem (alignedAddr + lane)
  | false => demonStep lane

/-- Schedule of fresh demonic byte valuations indexed by `(loadStep, laneIdx)`. -/
def DemonSched : Type := Nat → Nat → Nat

inductive MirOut (V M : Type) where
  | returned (v : V) (mem : M)
  | panicked (mem : M)
  | ub
  | diverges

inductive IsaOut (V M : Type) where
  | halted (v : V) (mem : M)
  | panicked (mem : M)
  | trap
  | diverges

/-- Total cross-level equivalence universally quantified over all per-load demonic
    over-read byte schedules `d : DemonSched`. -/
def TotalMirAsmDemonicEquiv {Q V M : Type}
    (ref : Q → MirOut V M) (asm : Q → DemonSched → IsaOut V M) : Prop :=
  ∀ q d,
    ref q ≠ MirOut.ub ∧
    asm q d ≠ IsaOut.trap ∧
    (∀ v m, asm q d = IsaOut.halted v m ↔ ref q = MirOut.returned v m) ∧
    (∀ m, asm q d = IsaOut.panicked m ↔ ref q = MirOut.panicked m) ∧
    (asm q d = IsaOut.diverges ↔ ref q = MirOut.diverges)

/-- Demonic Slack Obliviousness: the observable ISA outcome is invariant across
    all demonic byte valuations `d1, d2`. -/
def DemonicSlackOblivious {Q V M : Type}
    (asm : Q → DemonSched → IsaOut V M) : Prop :=
  ∀ q d1 d2, asm q d1 = asm q d2

def zeroDemon : DemonSched := fun _ _ => 0

/-- Theorem 7 (Demonic Slack Obliviousness Characterization):
    For any deterministic return-producing safe reference `ref`, `asm` satisfies
    `TotalMirAsmDemonicEquiv ref asm` iff `asm` is trap-free, `DemonicSlackOblivious`,
    and matches `ref` on `zeroDemon`. -/
theorem demonic_equiv_iff_slack_oblivious {Q V M : Type}
    (ref : Q → MirOut V M) (asm : Q → DemonSched → IsaOut V M)
    (hRefDet : ∀ q, ∃ v m, ref q = MirOut.returned v m) :
    TotalMirAsmDemonicEquiv ref asm ↔
      ((∀ q d, asm q d ≠ IsaOut.trap) ∧
       DemonicSlackOblivious asm ∧
       (∀ q v m, ref q = MirOut.returned v m → asm q zeroDemon = IsaOut.halted v m)) := by
  apply Iff.intro
  · intro hTot
    apply And.intro (fun q d => (hTot q d).2.1)
    apply And.intro
    · intro q d1 d2
      cases hRefDet q with
      | intro v hm =>
        cases hm with
        | intro m hr =>
          have h1 : asm q d1 = IsaOut.halted v m := ((hTot q d1).2.2.1 v m).2 hr
          have h2 : asm q d2 = IsaOut.halted v m := ((hTot q d2).2.2.1 v m).2 hr
          rw [h1, h2]
    · intro q v m hr
      exact ((hTot q zeroDemon).2.2.1 v m).2 hr
  · intro hParts q d
    cases hParts with
    | intro hNoTrap hRest =>
      cases hRest with
      | intro hObliv hZero =>
        cases hRefDet q with
        | intro v0 hm0 =>
          cases hm0 with
          | intro m0 hr0 =>
            have ha0 : asm q zeroDemon = IsaOut.halted v0 m0 := hZero q v0 m0 hr0
            have had : asm q d = IsaOut.halted v0 m0 := by
              rw [hObliv q d zeroDemon]
              exact ha0
            apply And.intro
            · rw [hr0]; intro h; cases h
            · apply And.intro (hNoTrap q d)
              apply And.intro
              · intro v m
                rw [had, hr0]
                exact Iff.intro
                  (fun h => by injection h with hv hm; subst hv; subst hm; rfl)
                  (fun h => by injection h with hv hm; subst hv; subst hm; rfl)
              · apply And.intro
                · intro m
                  rw [had, hr0]
                  exact Iff.intro (fun h => by cases h) (fun h => by cases h)
                · rw [had, hr0]
                  exact Iff.intro (fun h => by cases h) (fun h => by cases h)

-- ============================================================================
-- 4. Integer Bitmask Windowing (`packBits`, `shrxMask`, `bzhiMask`, `tzcntW`)
-- ============================================================================

def bitVal (b : Bool) : Nat :=
  match b with
  | true => 1
  | false => 0

/-- Packs `W` lane booleans `f 0 .. f (W - 1)` into a little-endian integer bitmask
    (`vpmovmskb` semantics: lane `i` occupies weight `2^i`). -/
def packBits (W : Nat) (f : Nat → Bool) : Nat :=
  @Nat.rec (fun _ => (Nat → Bool) → Nat)
    (fun _ => 0)
    (fun _ rec g => bitVal (g 0) + 2 * rec (fun i => g (i + 1)))
    W f

theorem packBits_zero (f : Nat → Bool) : packBits 0 f = 0 := rfl

theorem packBits_succ (n : Nat) (f : Nat → Bool) :
    packBits (n + 1) f = bitVal (f 0) + 2 * packBits n (fun i => f (i + 1)) := rfl

theorem packBits_congr :
    ∀ (W : Nat) (f g : Nat → Bool), (∀ i, i < W → f i = g i) → packBits W f = packBits W g
  | 0, _, _, _ => rfl
  | n + 1, f, g, hfg => by
    rw [packBits_succ, packBits_succ]
    have h0 : f 0 = g 0 := hfg 0 (Nat.zero_lt_succ n)
    have hrec : packBits n (fun i => f (i + 1)) = packBits n (fun i => g (i + 1)) :=
      packBits_congr n (fun i => f (i + 1)) (fun i => g (i + 1))
        (fun i hi => hfg (i + 1) (Nat.succ_lt_succ hi))
    rw [h0, hrec]

theorem packBits_lt_pow2 : ∀ (W : Nat) (f : Nat → Bool), packBits W f < pow2 W
  | 0, _ => by
    rw [packBits_zero, pow2_zero]
    exact Nat.zero_lt_succ 0
  | n + 1, f => by
    rw [packBits_succ, pow2_succ]
    have ih := packBits_lt_pow2 n (fun i => f (i + 1))
    let r := packBits n (fun i => f (i + 1))
    have hrr : r < pow2 n := ih
    have h2 : 2 * pow2 n = pow2 n + pow2 n := Nat.two_mul (pow2 n)
    have h2m : 2 * r = r + r := Nat.two_mul r
    change bitVal (f 0) + 2 * r < 2 * pow2 n
    rw [h2, h2m]
    cases f 0 with
    | false =>
      dsimp [bitVal]
      rw [Nat.zero_add]
      exact Nat.add_lt_add hrr hrr
    | true =>
      dsimp [bitVal]
      have hle1 : r + 1 ≤ pow2 n := hrr
      have hs1 : (r + 1) + r ≤ pow2 n + r := Nat.add_le_add_right hle1 r
      have hs2 : pow2 n + r < pow2 n + pow2 n := Nat.add_lt_add_left hrr (pow2 n)
      have hsum : (r + 1) + r < pow2 n + pow2 n := Nat.lt_of_le_of_lt hs1 hs2
      have hcomm : 1 + (r + r) = (r + 1) + r := by
        rw [← Nat.add_assoc, Nat.add_comm 1 r]
      rw [hcomm]
      exact hsum

/-- Logical right shift by `mis` bits (`shrx` semantics: `mask / 2^mis`). -/
def shrxMask (mis mask : Nat) : Nat :=
  Nat.div mask (pow2 mis)

/-- Low-`cnt` bit extraction (`bzhi` semantics: `mask % 2^cnt`). -/
def bzhiMask (cnt mask : Nat) : Nat :=
  Nat.mod mask (pow2 cnt)

theorem bit_add_two_mul_div_two (b : Bool) (rest : Nat) :
    Nat.div (bitVal b + 2 * rest) 2 = rest := by
  have hpos : 0 < 2 := Nat.zero_lt_succ 1
  have hdiv : Nat.div (bitVal b + 2 * rest) 2 = Nat.div (bitVal b) 2 + rest :=
    Nat.add_mul_div_left (bitVal b) rest hpos
  rw [hdiv]
  cases b with
  | false => exact Nat.zero_add rest
  | true => exact Nat.zero_add rest

theorem bit_add_two_mul_mod_two (b : Bool) (rest : Nat) :
    Nat.mod (bitVal b + 2 * rest) 2 = bitVal b := by
  have hmod : Nat.mod (bitVal b + 2 * rest) 2 = Nat.mod (bitVal b) 2 :=
    Nat.add_mul_mod_self_left (bitVal b) 2 rest
  rw [hmod]
  cases b <;> rfl

theorem shrxMask_packBits :
    ∀ (mis remW : Nat) (f : Nat → Bool),
      shrxMask mis (packBits (mis + remW) f) = packBits remW (fun j => f (mis + j))
  | 0, remW, f => by
    dsimp [shrxMask]
    rw [pow2_zero]
    have hd : Nat.div (packBits (0 + remW) f) 1 = packBits (0 + remW) f :=
      Nat.div_one (packBits (0 + remW) f)
    rw [hd, Nat.zero_add]
    exact packBits_congr remW f (fun j => f (0 + j)) (fun j _ => by rw [Nat.zero_add])
  | m + 1, remW, f => by
    dsimp [shrxMask]
    rw [Nat.succ_add, packBits_succ, pow2_succ]
    let num := bitVal (f 0) + 2 * packBits (m + remW) (fun i => f (i + 1))
    have hstep : Nat.div num (2 * pow2 m) = Nat.div (Nat.div num 2) (pow2 m) :=
      Eq.symm (Nat.div_div_eq_div_mul num 2 (pow2 m))
    change Nat.div num (2 * pow2 m) = packBits remW (fun j => f (m + 1 + j))
    rw [hstep]
    have h2 : Nat.div num 2 = packBits (m + remW) (fun i => f (i + 1)) :=
      bit_add_two_mul_div_two (f 0) (packBits (m + remW) (fun i => f (i + 1)))
    rw [h2]
    have ih := shrxMask_packBits m remW (fun i => f (i + 1))
    dsimp [shrxMask] at ih
    rw [ih]
    exact packBits_congr remW (fun j => f ((m + j) + 1)) (fun j => f (m + 1 + j))
      (fun j _ => by rw [Nat.add_assoc, Nat.add_comm j 1, ← Nat.add_assoc])

theorem bit_add_two_mul_mod_two_mul (b : Bool) (rest z : Nat) (hz : 0 < z) :
    Nat.mod (bitVal b + 2 * rest) (2 * z) = bitVal b + 2 * Nat.mod rest z := by
  let r := Nat.mod rest z
  let x := bitVal b + 2 * r
  have hx_lt : x < 2 * z := by
    have hr : r < z := Nat.mod_lt rest hz
    have h2z : 2 * z = z + z := Nat.two_mul z
    have h2r : 2 * r = r + r := Nat.two_mul r
    change bitVal b + 2 * r < 2 * z
    rw [h2z, h2r]
    cases b with
    | false =>
      dsimp [bitVal]
      rw [Nat.zero_add]
      exact Nat.add_lt_add hr hr
    | true =>
      dsimp [bitVal]
      have hr1 : r + 1 ≤ z := hr
      have hs1 : (r + 1) + r ≤ z + r := Nat.add_le_add_right hr1 r
      have hs2 : z + r < z + z := Nat.add_lt_add_left hr z
      have hs : (r + 1) + r < z + z := Nat.lt_of_le_of_lt hs1 hs2
      have hc : 1 + (r + r) = (r + 1) + r := by
        rw [← Nat.add_assoc, Nat.add_comm 1 r]
      rw [hc]
      exact hs
  have hdecomp : bitVal b + 2 * rest = x + (2 * z) * Nat.div rest z := by
    have hdm : z * Nat.div rest z + r = rest := Nat.div_add_mod rest z
    have h2dm : 2 * (z * Nat.div rest z + r) = 2 * rest :=
      congrArg (fun t => 2 * t) hdm
    rw [Nat.mul_add, ← Nat.mul_assoc] at h2dm
    rw [← h2dm]
    change bitVal b + (2 * z * Nat.div rest z + 2 * r) = (bitVal b + 2 * r) + (2 * z) * Nat.div rest z
    rw [Nat.add_comm (2 * z * Nat.div rest z) (2 * r), ← Nat.add_assoc]
  rw [hdecomp]
  have hmod1 : Nat.mod (x + (2 * z) * Nat.div rest z) (2 * z) = Nat.mod x (2 * z) :=
    Nat.add_mul_mod_self_left x (2 * z) (Nat.div rest z)
  have hmod2 : Nat.mod x (2 * z) = x := Nat.mod_eq_of_lt hx_lt
  rw [hmod1, hmod2]

theorem bzhiMask_packBits :
    ∀ (cnt extra : Nat) (f : Nat → Bool),
      bzhiMask cnt (packBits (cnt + extra) f) = packBits cnt f
  | 0, extra, f => by
    dsimp [bzhiMask]
    rw [pow2_zero, packBits_zero]
    exact Nat.mod_one (packBits (0 + extra) f)
  | c + 1, extra, f => by
    dsimp [bzhiMask]
    rw [Nat.succ_add, packBits_succ, packBits_succ, pow2_succ]
    rw [bit_add_two_mul_mod_two_mul (f 0) (packBits (c + extra) (fun i => f (i + 1)))
        (pow2 c) (pow2_pos c)]
    have ih := bzhiMask_packBits c extra (fun i => f (i + 1))
    dsimp [bzhiMask] at ih
    rw [ih]

/-- Theorem 8 (`shrx` + `bzhi` Exact Window Extraction):
    Shifting a `W`-lane mask right by `mis` and masking to `cnt` low bits (`mis + cnt ≤ W`)
    extracts the exact `cnt`-lane subwindow `f (mis + 0) .. f (mis + cnt - 1)`. -/
theorem shrx_bzhi_packBits_window
    (W mis cnt : Nat) (f : Nat → Bool) (hfit : mis + cnt ≤ W) :
    bzhiMask cnt (shrxMask mis (packBits W f)) =
      packBits cnt (fun j => f (mis + j)) := by
  let extra := W - (mis + cnt)
  have hW : W = mis + (cnt + extra) := by
    have h1 : (mis + cnt) + extra = W := Nat.add_sub_of_le hfit
    rw [← Nat.add_assoc]
    exact Eq.symm h1
  rw [hW]
  rw [shrxMask_packBits mis (cnt + extra) f]
  exact bzhiMask_packBits cnt extra (fun j => f (mis + j))

/-- Theorem 9 (Demonic Slack Erasure under Window Masking):
    Whenever `[alignedAddr + mis, alignedAddr + mis + cnt) ⊆ [authBase, authBase + authLen)`
    and `mis + cnt ≤ pow2 k`, the `shrx` + `bzhi` masked comparison bitmask depends
    exclusively on authorized slice bytes and is 100% oblivious to `demonStep`. -/
theorem masked_demonic_chunk_eq_pure_slice_window
    (k authBase authLen alignedAddr mis cnt needle : Nat)
    (mem : Nat → Nat) (demonStep : Nat → Nat)
    (hfit : mis + cnt ≤ pow2 k)
    (hlo : authBase ≤ alignedAddr + mis)
    (hhi : alignedAddr + mis + cnt ≤ authBase + authLen) :
    bzhiMask cnt
      (shrxMask mis
        (packBits (pow2 k)
          (fun i => Nat.beq (demonicReadLane authBase authLen mem demonStep alignedAddr i) needle))) =
      packBits cnt (fun j => Nat.beq (mem (alignedAddr + mis + j)) needle) := by
  rw [shrx_bzhi_packBits_window (pow2 k) mis cnt _ hfit]
  apply packBits_congr cnt
  intro j hj
  dsimp [demonicReadLane]
  have haddr : alignedAddr + (mis + j) = alignedAddr + mis + j :=
    Eq.symm (Nat.add_assoc alignedAddr mis j)
  rw [haddr]
  have hj_lo : authBase ≤ alignedAddr + mis + j :=
    Nat.le_trans hlo (Nat.le_add_right (alignedAddr + mis) j)
  have hj_hi : alignedAddr + mis + j < authBase + authLen :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj (alignedAddr + mis)) hhi
  have hble : Nat.ble authBase (alignedAddr + mis + j) = true :=
    Eq.mpr Nat.ble_eq hj_lo
  have hblt : Nat.blt (alignedAddr + mis + j) (authBase + authLen) = true :=
    Eq.mpr Nat.ble_eq hj_hi
  have hin : inSlice authBase authLen (alignedAddr + mis + j) = true := by
    dsimp [inSlice]
    rw [hble, hblt]
    rfl
  rw [hin]

/-- Theorem 10 (Negative Canary: Off-by-One Mask Fails Demonic Slack Obliviousness):
    If an aligned over-read kernel masks `len + 1` bits instead of `len` bits (e.g., `len = 1`
    masked with `cnt = 2` at `ptr = 0`), two demonic valuations (`0` vs. `needle = 165` at
    slack lane `1`) yield distinct return values, refuting both `DemonicSlackOblivious`
    and `TotalMirAsmDemonicEquiv`. -/
def offByOneAsm (mem : Nat → Nat) (q : Nat) (d : DemonSched) : IsaOut Bool Unit :=
  let mask := bzhiMask 2
    (packBits 4 (fun i => Nat.beq (demonicReadLane 0 1 mem (d 0) 0 i) q))
  IsaOut.halted (match Nat.beq mask 0 with | true => false | false => true) ()

def soundRef1Byte (mem : Nat → Nat) (q : Nat) : MirOut Bool Unit :=
  MirOut.returned (Nat.beq (mem 0) q) ()

theorem off_by_one_mask_violates_demonic_equiv :
    ¬ DemonicSlackOblivious (offByOneAsm (fun _ => 0)) ∧
    ¬ TotalMirAsmDemonicEquiv (soundRef1Byte (fun _ => 0)) (offByOneAsm (fun _ => 0)) := by
  let dZero : DemonSched := fun _ _ => 0
  let dHit : DemonSched := fun _ lane => match Nat.beq lane 1 with | true => 165 | false => 0
  have hDiff : offByOneAsm (fun _ => 0) 165 dZero ≠ offByOneAsm (fun _ => 0) 165 dHit := by
    intro hEq
    cases hEq
  apply And.intro
  · intro hObliv
    exact hDiff (hObliv 165 dZero dHit)
  · intro hTot
    have h1 := ((hTot 165 dHit).2.2.1 false ()).2 rfl
    cases h1

/-- Microarchitectural leakage observation for 2-safety constant-time analysis. -/
inductive LeakObs where
  | branch (taken : Bool)

/-- Unmasked fast-path branch (`glibc` `testl %eax, %eax; jnz check_masked` idiom):
    branches on the unmasked 2-lane `vpmovmskb` BEFORE applying the 1-lane slice mask. -/
def unmaskedFastpathSearch (needle pubByte secSlack : Nat) : Bool × List LeakObs :=
  let rawMask := packBits 2 (fun i =>
    match i with
    | 0 => Nat.beq pubByte needle
    | _ => Nat.beq secSlack needle)
  match Nat.beq rawMask 0 with
  | true => (false, [LeakObs.branch false])
  | false =>
    let masked := bzhiMask 1 rawMask
    (match Nat.beq masked 0 with | true => false | false => true, [LeakObs.branch true])

/-- Masked-first branch: masks out demonic/secret slack BEFORE any control-flow branch. -/
def maskedFirstSearch (needle pubByte secSlack : Nat) : Bool × List LeakObs :=
  let rawMask := packBits 2 (fun i =>
    match i with
    | 0 => Nat.beq pubByte needle
    | _ => Nat.beq secSlack needle)
  let masked := bzhiMask 1 rawMask
  match Nat.beq masked 0 with
  | true => (false, [LeakObs.branch false])
  | false => (true, [LeakObs.branch true])

/-- Theorem 11 (1-Safety vs. 2-Safety Split on Unmasked Over-Read Branches):
    Branching on unmasked `vpmovmskb` before masking preserves 1-safety slack
    obliviousness (`∀ s1 s2, .1` agrees), YET violates 2-safety `LeakTrace`
    non-interference when an adjacent caller secret `secSlack` shares the same
    aligned chunk (`secSlack = 0` vs `secSlack = 165`), whereas masking BEFORE
    branching satisfies both 1-safety and 2-safety! -/
theorem unmasked_fastpath_1safety_vs_2safety_leaktrace :
    (∀ needle pubByte s1 s2,
      (unmaskedFastpathSearch needle pubByte s1).1 =
      (unmaskedFastpathSearch needle pubByte s2).1) ∧
    (unmaskedFastpathSearch 165 0 0).2 ≠ (unmaskedFastpathSearch 165 0 165).2 ∧
    (∀ needle pubByte s1 s2,
      maskedFirstSearch needle pubByte s1 = maskedFirstSearch needle pubByte s2) := by
  apply And.intro
  · intro needle pubByte s1 s2
    dsimp [unmaskedFastpathSearch, packBits, bitVal, bzhiMask, pow2]
    cases Nat.beq pubByte needle <;>
      cases Nat.beq s1 needle <;>
      cases Nat.beq s2 needle <;> rfl
  · apply And.intro
    · intro hEq
      cases hEq
    · intro needle pubByte s1 s2
      dsimp [maskedFirstSearch, packBits, bitVal, bzhiMask, pow2]
      cases Nat.beq pubByte needle <;>
        cases Nat.beq s1 needle <;>
        cases Nat.beq s2 needle <;> rfl

-- ============================================================================
-- 5. `tzcnt` vs. `bsf` (`CpuFeatures.bmi1`) and First-Set-Bit Extraction
-- ============================================================================

/-- Bounded `W`-bit trailing-zero count (`tzcnt` with width `W`): returns `W` when
    `mask = 0`, else the index `0 .. W - 1` of the least-significant `1` bit. -/
def tzcntW (W mask : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat)
    (fun _ => 0)
    (fun w rec m =>
      match Nat.beq m 0 with
      | true => w + 1
      | false =>
        match Nat.beq (Nat.mod m 2) 1 with
        | true => 0
        | false => 1 + rec (Nat.div m 2))
    W mask

theorem tzcntW_zero_width (mask : Nat) : tzcntW 0 mask = 0 := rfl

theorem tzcntW_succ (w mask : Nat) :
    tzcntW (w + 1) mask =
      match Nat.beq mask 0 with
      | true => w + 1
      | false =>
        match Nat.beq (Nat.mod mask 2) 1 with
        | true => 0
        | false => 1 + tzcntW w (Nat.div mask 2) := rfl

theorem tzcntW_on_zero (W : Nat) : tzcntW W 0 = W := by
  cases W with
  | zero => rfl
  | succ w => rfl

/-- Exact hardware semantics of x86 `F3 0F BC` (`tzcnt` when `hasBmi1 = true`;
    `bsf` leaving destination unmodified as `prevDst` on `mask = 0` when `hasBmi1 = false`). -/
def x86TzcntOrBsf32 (hasBmi1 : Bool) (prevDst mask : Nat) : Nat :=
  match Nat.beq mask 0 with
  | true =>
    match hasBmi1 with
    | true => 32
    | false => prevDst
  | false => tzcntW 32 mask

/-- `glibc` `memchr-avx2.S` `L(first_vec_x0)` tail check (`tzcntl %eax, %eax; cmpl %eax, %edx`). -/
def glibcFirstVecTail (hasBmi1 : Bool) (len mask : Nat) : Option Nat :=
  let idx := x86TzcntOrBsf32 hasBmi1 mask mask
  match Nat.blt idx len with
  | true => some idx
  | false => none

/-- Theorem 12 (`CpuFeatures.bmi1` `tzcnt` vs. `bsf` Zero-Input Hazard):
    1. With `hasBmi1 = true`, `glibcFirstVecTail` returns `none` on `mask = 0` for all `len ≤ 32`;
    2. With `hasBmi1 = false`, `glibcFirstVecTail false 1 0 = some 0` (false match on zero mask!);
    3. Guarding `tzcnt`/`bsf` behind `mask == 0` eliminates the `hasBmi1` dependence completely. -/
theorem bmi1_tzcnt_vs_bsf_zero_hazard :
    (∀ len, len ≤ 32 → glibcFirstVecTail true len 0 = none) ∧
    glibcFirstVecTail false 1 0 = some 0 ∧
    (∀ b1 b2 p1 p2 mask,
      (match Nat.beq mask 0 with | true => none | false => some (x86TzcntOrBsf32 b1 p1 mask)) =
      (match Nat.beq mask 0 with | true => none | false => some (x86TzcntOrBsf32 b2 p2 mask))) := by
  apply And.intro
  · intro len hle
    dsimp [glibcFirstVecTail, x86TzcntOrBsf32, Nat.blt]
    have hnot : Nat.ble 33 len = false := by
      cases hle33 : Nat.ble 33 len with
      | false => rfl
      | true =>
        have hlt : 32 < len := Eq.mp Nat.ble_eq hle33
        exact False.elim (Nat.not_lt_of_ge hle hlt)
    rw [hnot]
  · apply And.intro rfl
    intro b1 b2 p1 p2 mask
    cases hm : Nat.beq mask 0 with
    | true => rfl
    | false =>
      dsimp [x86TzcntOrBsf32]
      rw [hm]

theorem packBits_eq_zero_iff :
    ∀ (cnt : Nat) (g : Nat → Bool),
      packBits cnt g = 0 ↔ (∀ j, j < cnt → g j = false)
  | 0, g =>
    Iff.intro
      (fun _ j hj => by cases hj)
      (fun _ => rfl)
  | c + 1, g => by
    rw [packBits_succ]
    apply Iff.intro
    · intro h0 j hj
      cases hg0 : g 0 with
      | true =>
        rw [hg0] at h0
        dsimp [bitVal] at h0
        have hpos : 0 < 1 + 2 * packBits c (fun i => g (i + 1)) := by
          rw [Nat.add_comm]
          exact Nat.zero_lt_succ _
        rw [h0] at hpos
        cases hpos
      | false =>
        rw [hg0] at h0
        dsimp [bitVal] at h0
        rw [Nat.zero_add] at h0
        have hrest0 : packBits c (fun i => g (i + 1)) = 0 := by
          cases hrc : packBits c (fun i => g (i + 1)) with
          | zero => rfl
          | succ k =>
            rw [hrc] at h0
            have h2k : 2 * (k + 1) = 2 * k + 2 := rfl
            rw [h2k] at h0
            cases h0
        cases j with
        | zero => exact hg0
        | succ j' =>
          exact (packBits_eq_zero_iff c (fun i => g (i + 1))).1 hrest0 j'
            (Nat.lt_of_succ_lt_succ hj)
    · intro hall
      have hg0 : g 0 = false := hall 0 (Nat.zero_lt_succ c)
      have hrest : packBits c (fun i => g (i + 1)) = 0 :=
        (packBits_eq_zero_iff c (fun i => g (i + 1))).2
          (fun j hj => hall (j + 1) (Nat.succ_lt_succ hj))
      rw [hg0, hrest]
      rfl

/-- Fundamental First-Set-Bit Correctness of `tzcntW` over `packBits cnt g`:
    Whenever `cnt ≤ W` and `packBits cnt g ≠ 0`, `k := tzcntW W (packBits cnt g)`
    satisfies `k < cnt`, `g k = true`, and `∀ j < k, g j = false`. -/
theorem tzcntW_packBits_first_match :
    ∀ (cnt W : Nat) (g : Nat → Bool),
      cnt ≤ W →
      packBits cnt g ≠ 0 →
      tzcntW W (packBits cnt g) < cnt ∧
      g (tzcntW W (packBits cnt g)) = true ∧
      (∀ j, j < tzcntW W (packBits cnt g) → g j = false)
  | 0, _, _, _, hne => False.elim (hne rfl)
  | c + 1, 0, _, hle, _ => by cases hle
  | c + 1, w + 1, g, hle, hne => by
    have hcw : c ≤ w := Nat.le_of_succ_le_succ hle
    have hbeq0 : Nat.beq (packBits (c + 1) g) 0 = false := by
      cases hb : Nat.beq (packBits (c + 1) g) 0 with
      | false => rfl
      | true => exact False.elim (hne (Nat.eq_of_beq_eq_true hb))
    rw [tzcntW_succ, hbeq0]
    dsimp
    have hp : packBits (c + 1) g =
        bitVal (g 0) + 2 * packBits c (fun i => g (i + 1)) :=
      packBits_succ c g
    cases hg0 : g 0 with
    | true =>
      have hmod1 : Nat.mod (packBits (c + 1) g) 2 = 1 := by
        rw [hp, bit_add_two_mul_mod_two, hg0]
        rfl
      rw [hmod1]
      dsimp
      exact And.intro (Nat.zero_lt_succ c) (And.intro hg0 (fun _ hj => by cases hj))
    | false =>
      have hmod0 : Nat.mod (packBits (c + 1) g) 2 = 0 := by
        rw [hp, bit_add_two_mul_mod_two, hg0]
        rfl
      have hdiv : Nat.div (packBits (c + 1) g) 2 = packBits c (fun i => g (i + 1)) := by
        rw [hp, bit_add_two_mul_div_two]
      have hrest_ne : packBits c (fun i => g (i + 1)) ≠ 0 := by
        intro hr0
        apply hne
        rw [hp, hg0, hr0]
        rfl
      rw [hmod0, hdiv]
      dsimp
      have hcomm : 1 + tzcntW w (packBits c (fun i => g (i + 1))) =
          tzcntW w (packBits c (fun i => g (i + 1))) + 1 :=
        Nat.add_comm 1 _
      rw [hcomm]
      have ih := tzcntW_packBits_first_match c w (fun i => g (i + 1)) hcw hrest_ne
      apply And.intro (Nat.succ_lt_succ ih.1)
      apply And.intro ih.2.1
      intro j hj
      cases j with
      | zero => exact hg0
      | succ j' =>
        exact ih.2.2 j' (Nat.lt_of_succ_lt_succ hj)

-- ============================================================================
-- 6. Variable-Stride Early-Exit Search Equivalence (`early_exit_simd_search_equiv`)
-- ============================================================================

/-- Reference scalar early-exiting byte-by-byte search loop. -/
def scalarSearchLoop (pred : Nat → Bool) (mem : Nat → Nat) (ptr rem idx : Nat) : Option Nat :=
  @Nat.rec (fun _ => Nat → Option Nat)
    (fun _ => none)
    (fun _ rec curIdx =>
      match pred (mem (ptr + curIdx)) with
      | true => some curIdx
      | false => rec (curIdx + 1))
    rem idx

theorem scalarSearchLoop_zero (pred : Nat → Bool) (mem : Nat → Nat) (ptr idx : Nat) :
    scalarSearchLoop pred mem ptr 0 idx = none := rfl

theorem scalarSearchLoop_succ (pred : Nat → Bool) (mem : Nat → Nat) (ptr r idx : Nat) :
    scalarSearchLoop pred mem ptr (r + 1) idx =
      match pred (mem (ptr + idx)) with
      | true => some idx
      | false => scalarSearchLoop pred mem ptr r (idx + 1) := rfl

/-- Safe Rust `memchr` reference specification over `[ptr, ptr + len)`. -/
def memchrRef (needle : Nat) (mem : Nat → Nat) (ptr len : Nat) : Option Nat :=
  scalarSearchLoop (fun b => Nat.beq b needle) mem ptr len 0

theorem scalarSearchLoop_skip_false :
    ∀ (cnt rem idx : Nat) (pred : Nat → Bool) (mem : Nat → Nat) (ptr : Nat),
      cnt ≤ rem →
      (∀ j, j < cnt → pred (mem (ptr + (idx + j))) = false) →
      scalarSearchLoop pred mem ptr rem idx =
        scalarSearchLoop pred mem ptr (rem - cnt) (idx + cnt)
  | 0, rem, idx, pred, mem, ptr, _, _ => by
    rw [Nat.sub_zero, Nat.add_zero]
  | c + 1, 0, _, _, _, _, hle, _ => by cases hle
  | c + 1, r + 1, idx, pred, mem, ptr, hle, hall => by
    rw [scalarSearchLoop_succ]
    have h0 : pred (mem (ptr + idx)) = false := by
      have h0' := hall 0 (Nat.zero_lt_succ c)
      rw [Nat.add_zero] at h0'
      exact h0'
    rw [h0]
    dsimp
    have hcr : c ≤ r := Nat.le_of_succ_le_succ hle
    have ih := scalarSearchLoop_skip_false c r (idx + 1) pred mem ptr hcr
      (fun j hj => by
        have hj' := hall (j + 1) (Nat.succ_lt_succ hj)
        have hassoc : idx + 1 + j = idx + (j + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 j]
        rw [hassoc]
        exact hj')
    rw [ih, Nat.succ_sub_succ]
    have hassoc2 : idx + 1 + c = idx + (c + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 c]
    rw [hassoc2]

theorem scalarSearchLoop_hit_at :
    ∀ (k rem idx : Nat) (pred : Nat → Bool) (mem : Nat → Nat) (ptr : Nat),
      k < rem →
      pred (mem (ptr + (idx + k))) = true →
      (∀ j, j < k → pred (mem (ptr + (idx + j))) = false) →
      scalarSearchLoop pred mem ptr rem idx = some (idx + k)
  | k, rem, idx, pred, mem, ptr, hlt, hhit, hpre => by
    have hle : k ≤ rem := Nat.le_of_lt hlt
    rw [scalarSearchLoop_skip_false k rem idx pred mem ptr hle hpre]
    have hpos : 0 < rem - k := Nat.sub_pos_of_lt hlt
    cases hsub : rem - k with
    | zero =>
      rw [hsub] at hpos
      cases hpos
    | succ r' =>
      rw [scalarSearchLoop_succ, hhit]

/-- Theorem 13 (Variable-Stride Early-Exit Window Simulation):
    Simulates between `1` and `cnt` scalar `memchr` steps against a single
    `cnt`-lane bitmask `m = packBits cnt (fun j => pred (mem (ptr + (idx + j))))`. -/
theorem scalarSearchLoop_window_step
    (W cnt rem idx : Nat) (pred : Nat → Bool) (mem : Nat → Nat) (ptr : Nat)
    (hcntW : cnt ≤ W) (hcntRem : cnt ≤ rem) :
    let m := packBits cnt (fun j => pred (mem (ptr + (idx + j))))
    scalarSearchLoop pred mem ptr rem idx =
      match Nat.beq m 0 with
      | true => scalarSearchLoop pred mem ptr (rem - cnt) (idx + cnt)
      | false => some (idx + tzcntW W m) := by
  intro m
  cases hm0 : Nat.beq m 0 with
  | true =>
    have hmz : m = 0 := Nat.eq_of_beq_eq_true hm0
    have hall : ∀ j, j < cnt → pred (mem (ptr + (idx + j))) = false :=
      (packBits_eq_zero_iff cnt (fun j => pred (mem (ptr + (idx + j))))).1 hmz
    exact scalarSearchLoop_skip_false cnt rem idx pred mem ptr hcntRem hall
  | false =>
    have hmne : m ≠ 0 := by
      intro hz
      rw [hz] at hm0
      cases hm0
    have htz := tzcntW_packBits_first_match cnt W
      (fun j => pred (mem (ptr + (idx + j)))) hcntW hmne
    have hkRem : tzcntW W m < rem := Nat.lt_of_lt_of_le htz.1 hcntRem
    exact scalarSearchLoop_hit_at (tzcntW W m) rem idx pred mem ptr hkRem htz.2.1 htz.2.2

/-- Executable boolean check for `GranuleLoadAdmissible`: checks `k ≤ granuleBits`,
    `alignedAddr % 2^k == 0`, and non-empty interval overlap
    `max(alignedAddr, authBase) < min(alignedAddr + 2^k, authBase + authLen)`. -/
def granuleLoadAdmissibleBool
    (granuleBits authBase authLen k alignedAddr : Nat) : Bool :=
  let lo := match Nat.ble alignedAddr authBase with | true => authBase | false => alignedAddr
  let hiA := alignedAddr + pow2 k
  let hiB := authBase + authLen
  let hi := match Nat.ble hiA hiB with | true => hiA | false => hiB
  Nat.ble k granuleBits &&
  Nat.beq (Nat.mod alignedAddr (pow2 k)) 0 &&
  Nat.blt lo hi

/-- Soundness of the runtime granule-check guard: `granuleLoadAdmissibleBool = true`
    witnesses `GranuleLoadAdmissible` (`lo` is an explicit authorized in-span byte!). -/
theorem granuleLoadAdmissibleBool_sound
    (granuleBits authBase authLen k alignedAddr : Nat)
    (hok : granuleLoadAdmissibleBool granuleBits authBase authLen k alignedAddr = true) :
    GranuleLoadAdmissible granuleBits authBase authLen k alignedAddr := by
  dsimp [granuleLoadAdmissibleBool] at hok
  cases hk : Nat.ble k granuleBits with
  | false => rw [hk] at hok; cases hok
  | true =>
    rw [hk] at hok
    cases hm : Nat.beq (Nat.mod alignedAddr (pow2 k)) 0 with
    | false => rw [hm] at hok; cases hok
    | true =>
      rw [hm] at hok
      let lo := match Nat.ble alignedAddr authBase with | true => authBase | false => alignedAddr
      let hiA := alignedAddr + pow2 k
      let hiB := authBase + authLen
      let hi := match Nat.ble hiA hiB with | true => hiA | false => hiB
      have hlt : lo < hi := Eq.mp Nat.ble_eq hok
      have hloA : alignedAddr ≤ lo := by
        dsimp [lo]
        cases hcmp : Nat.ble alignedAddr authBase with
        | true => exact Eq.mp Nat.ble_eq hcmp
        | false => exact Nat.le_refl alignedAddr
      have hloB : authBase ≤ lo := by
        dsimp [lo]
        cases hcmp : Nat.ble alignedAddr authBase with
        | true => exact Nat.le_refl authBase
        | false =>
          cases Nat.lt_or_ge authBase alignedAddr with
          | inl h => exact Nat.le_of_lt h
          | inr h =>
            have hc : Nat.ble alignedAddr authBase = true := Eq.mpr Nat.ble_eq h
            rw [hc] at hcmp; cases hcmp
      have hhiA : hi ≤ hiA := by
        dsimp [hi]
        cases hcmp : Nat.ble hiA hiB with
        | true => exact Nat.le_refl hiA
        | false =>
          cases Nat.lt_or_ge hiB hiA with
          | inl h => exact Nat.le_of_lt h
          | inr h =>
            have hc : Nat.ble hiA hiB = true := Eq.mpr Nat.ble_eq h
            rw [hc] at hcmp; cases hcmp
      have hhiB : hi ≤ hiB := by
        dsimp [hi]
        cases hcmp : Nat.ble hiA hiB with
        | true => exact Eq.mp Nat.ble_eq hcmp
        | false => exact Nat.le_refl hiB
      exact And.intro (Eq.mp Nat.ble_eq hk)
        (And.intro (Nat.eq_of_beq_eq_true hm)
          (Exists.intro lo
            (And.intro hloA
              (And.intro (Nat.lt_of_lt_of_le hlt hhiA)
                (And.intro hloB (Nat.lt_of_lt_of_le hlt hhiB))))))

theorem granuleLoadAdmissibleBool_of_witness
    (granuleBits authBase authLen k alignedAddr b : Nat)
    (hkle : k ≤ granuleBits)
    (hmod : Nat.mod alignedAddr (pow2 k) = 0)
    (hb1 : alignedAddr ≤ b) (hb2 : b < alignedAddr + pow2 k)
    (hb3 : authBase ≤ b) (hb4 : b < authBase + authLen) :
    granuleLoadAdmissibleBool granuleBits authBase authLen k alignedAddr = true := by
  dsimp [granuleLoadAdmissibleBool]
  have hk : Nat.ble k granuleBits = true := Eq.mpr Nat.ble_eq hkle
  have hm : Nat.beq (Nat.mod alignedAddr (pow2 k)) 0 = true := by
    rw [hmod]; rfl
  rw [hk, hm]
  let lo := match Nat.ble alignedAddr authBase with | true => authBase | false => alignedAddr
  let hiA := alignedAddr + pow2 k
  let hiB := authBase + authLen
  let hi := match Nat.ble hiA hiB with | true => hiA | false => hiB
  have hlo_le_b : lo ≤ b := by
    dsimp [lo]
    cases Nat.ble alignedAddr authBase with
    | true => exact hb3
    | false => exact hb1
  have hb_lt_hi : b < hi := by
    dsimp [hi]
    cases Nat.ble hiA hiB with
    | true => exact hb2
    | false => exact hb4
  have hlo_lt_hi : lo < hi := Nat.lt_of_le_of_lt hlo_le_b hb_lt_hi
  exact Eq.mpr Nat.ble_eq hlo_lt_hi

inductive IsaSearchOut where
  | ok (res : Option Nat)
  | trap

/-- Executes one checked `2^k`-byte `DemonicGranuleLoad` + `vpcmpeqb` + `vpmovmskb`
    at `alignedAddr`, trapping if the hardware granule contract is violated. -/
def checkedDemonicChunkMask
    (granuleBits authBase authLen k needle : Nat)
    (mem : Nat → Nat) (demonStep : Nat → Nat) (alignedAddr : Nat) : Option Nat :=
  match granuleLoadAdmissibleBool granuleBits authBase authLen k alignedAddr with
  | true =>
    some (packBits (pow2 k)
      (fun i => Nat.beq (demonicReadLane authBase authLen mem demonStep alignedAddr i) needle))
  | false => none

/-- Aligned main loop + masked epilog (`rem ≥ 1`, `cur = ptr + idx` is `2^k`-aligned):
    fuel-bounded by `fuel ≥ rem` via `Nat.rec` (zero `._unsafe_rec`). -/
def simdAlignedLoopAndEpilog
    (granuleBits ptr len k needle : Nat)
    (mem : Nat → Nat) (demon : DemonSched)
    (fuel step cur idx rem : Nat) : IsaSearchOut :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat → IsaSearchOut)
    (fun _ _ _ _ => IsaSearchOut.trap)
    (fun _ rec st cAddr cIdx r =>
      let W := pow2 k
      match checkedDemonicChunkMask granuleBits ptr len k needle mem (demon st) cAddr with
      | none => IsaSearchOut.trap
      | some rawMask =>
        match Nat.ble r W with
        | true =>
          let mTail := bzhiMask r rawMask
          match Nat.beq mTail 0 with
          | true => IsaSearchOut.ok none
          | false => IsaSearchOut.ok (some (cIdx + tzcntW W mTail))
        | false =>
          match Nat.beq rawMask 0 with
          | true => rec (st + 1) (cAddr + W) (cIdx + W) (r - W)
          | false => IsaSearchOut.ok (some (cIdx + tzcntW W rawMask)))
    fuel step cur idx rem

theorem simdAlignedLoopAndEpilog_succ
    (granuleBits ptr len k needle : Nat)
    (mem : Nat → Nat) (demon : DemonSched)
    (f step cur idx rem : Nat) :
    simdAlignedLoopAndEpilog granuleBits ptr len k needle mem demon (f + 1) step cur idx rem =
      match checkedDemonicChunkMask granuleBits ptr len k needle mem (demon step) cur with
      | none => IsaSearchOut.trap
      | some rawMask =>
        match Nat.ble rem (pow2 k) with
        | true =>
          let mTail := bzhiMask rem rawMask
          match Nat.beq mTail 0 with
          | true => IsaSearchOut.ok none
          | false => IsaSearchOut.ok (some (idx + tzcntW (pow2 k) mTail))
        | false =>
          match Nat.beq rawMask 0 with
          | true =>
            simdAlignedLoopAndEpilog granuleBits ptr len k needle mem demon
              f (step + 1) (cur + pow2 k) (idx + pow2 k) (rem - pow2 k)
          | false => IsaSearchOut.ok (some (idx + tzcntW (pow2 k) rawMask)) := rfl

/-- Complete 4-stage aligned-overread SIMD `memchr`:
    1. Empty-slice guard (`len == 0 -> ok none`);
    2. Misaligned masked prolog at `algn = alignDown k ptr` (`shrx mis` + `bzhi firstCnt`);
    3. `2^k`-aligned main loop (`rem > 2^k`);
    4. `2^k`-aligned masked epilog (`1 ≤ rem ≤ 2^k`). -/
def simdAlignedOverreadSearch
    (granuleBits k needle : Nat)
    (mem : Nat → Nat) (demon : DemonSched)
    (ptr len : Nat) : IsaSearchOut :=
  match Nat.beq len 0 with
  | true => IsaSearchOut.ok none
  | false =>
    let W := pow2 k
    let algn := alignDown k ptr
    let mis := ptr - algn
    let remFirst := W - mis
    match checkedDemonicChunkMask granuleBits ptr len k needle mem (demon 0) algn with
    | none => IsaSearchOut.trap
    | some raw0 =>
      let shifted := shrxMask mis raw0
      match Nat.ble len remFirst with
      | true =>
        let m0 := bzhiMask len shifted
        match Nat.beq m0 0 with
        | true => IsaSearchOut.ok none
        | false => IsaSearchOut.ok (some (tzcntW W m0))
      | false =>
        match Nat.beq shifted 0 with
        | true =>
          let remAfter := len - remFirst
          simdAlignedLoopAndEpilog
            granuleBits ptr len k needle mem demon
            remAfter 1 (algn + W) remFirst remAfter
        | false => IsaSearchOut.ok (some (tzcntW W shifted))

theorem simdAlignedLoopAndEpilog_equiv
    (granuleBits ptr len k needle : Nat)
    (mem : Nat → Nat) (demon : DemonSched)
    (hkle : k ≤ granuleBits) :
    ∀ (fuel step cur idx rem : Nat),
      rem ≤ fuel →
      1 ≤ rem →
      cur = ptr + idx →
      idx + rem = len →
      Nat.mod cur (pow2 k) = 0 →
      simdAlignedLoopAndEpilog granuleBits ptr len k needle mem demon fuel step cur idx rem =
        IsaSearchOut.ok (scalarSearchLoop (fun b => Nat.beq b needle) mem ptr rem idx)
  | 0, _, _, _, rem, hfuel, hrem, _, _, _ => by
    have h0 : rem = 0 := Nat.eq_zero_of_le_zero hfuel
    rw [h0] at hrem
    cases hrem
  | f + 1, step, cur, idx, rem, hfuel, hrem, hcur, hsum, hmod => by
    rw [simdAlignedLoopAndEpilog_succ]
    have hb1 : cur ≤ cur := Nat.le_refl cur
    have hb2 : cur < cur + pow2 k := by
      have hp := pow2_pos k
      have h0 : cur + 0 < cur + pow2 k := Nat.add_lt_add_left hp cur
      rw [Nat.add_zero] at h0
      exact h0
    have hb3 : ptr ≤ cur := by
      rw [hcur]
      exact Nat.le_add_right ptr idx
    have hb4 : cur < ptr + len := by
      rw [hcur, ← hsum, ← Nat.add_assoc]
      have h0 : ptr + idx + 0 < ptr + idx + rem := Nat.add_lt_add_left hrem (ptr + idx)
      rw [Nat.add_zero] at h0
      exact h0
    have hadm : granuleLoadAdmissibleBool granuleBits ptr len k cur = true :=
      granuleLoadAdmissibleBool_of_witness granuleBits ptr len k cur cur
        hkle hmod hb1 hb2 hb3 hb4
    have hchk :
        checkedDemonicChunkMask granuleBits ptr len k needle mem (demon step) cur =
          some (packBits (pow2 k)
            (fun i => Nat.beq (demonicReadLane ptr len mem (demon step) cur i) needle)) := by
      dsimp [checkedDemonicChunkMask]
      rw [hadm]
    rw [hchk]
    dsimp
    cases hleW : Nat.ble rem (pow2 k) with
    | true =>
      dsimp
      have hrW : rem ≤ pow2 k := Eq.mp Nat.ble_eq hleW
      have hfit : 0 + rem ≤ pow2 k := by rw [Nat.zero_add]; exact hrW
      have hlo : ptr ≤ cur + 0 := by rw [Nat.add_zero]; exact hb3
      have hhi : cur + 0 + rem ≤ ptr + len := by
        rw [Nat.add_zero, hcur, Nat.add_assoc, hsum]
        exact Nat.le_refl (ptr + len)
      have hmaskEq :
          bzhiMask rem
            (packBits (pow2 k)
              (fun i => Nat.beq (demonicReadLane ptr len mem (demon step) cur i) needle)) =
            packBits rem (fun j => Nat.beq (mem (ptr + (idx + j))) needle) := by
        have hm0 := masked_demonic_chunk_eq_pure_slice_window
          k ptr len cur 0 rem needle mem (demon step) hfit hlo hhi
        have hsh0 : ∀ x, shrxMask 0 x = x := by
          intro x
          dsimp [shrxMask]
          rw [pow2_zero]
          exact Nat.div_one x
        rw [hsh0] at hm0
        rw [hm0]
        apply packBits_congr rem
        intro j _
        rw [Nat.add_zero, hcur, Nat.add_assoc]
      rw [hmaskEq]
      have hwin := scalarSearchLoop_window_step (pow2 k) rem rem idx
        (fun b => Nat.beq b needle) mem ptr hrW (Nat.le_refl rem)
      dsimp at hwin
      rw [hwin, Nat.sub_self, scalarSearchLoop_zero]
      cases Nat.beq (packBits rem (fun j => Nat.beq (mem (ptr + (idx + j))) needle)) 0 <;> rfl
    | false =>
      dsimp
      have hgtW : pow2 k < rem := by
        cases Nat.lt_or_ge (pow2 k) rem with
        | inl h => exact h
        | inr h =>
          have hc : Nat.ble rem (pow2 k) = true := Eq.mpr Nat.ble_eq h
          rw [hc] at hleW; cases hleW
      have hWleRem : pow2 k ≤ rem := Nat.le_of_lt hgtW
      have hfit : 0 + pow2 k ≤ pow2 k := by rw [Nat.zero_add]; exact Nat.le_refl (pow2 k)
      have hlo : ptr ≤ cur + 0 := by rw [Nat.add_zero]; exact hb3
      have hhi : cur + 0 + pow2 k ≤ ptr + len := by
        rw [Nat.add_zero, hcur, Nat.add_assoc, ← hsum]
        exact Nat.add_le_add_left (Nat.add_le_add_left hWleRem idx) ptr
      have hrawEq :
          packBits (pow2 k)
            (fun i => Nat.beq (demonicReadLane ptr len mem (demon step) cur i) needle) =
            packBits (pow2 k) (fun j => Nat.beq (mem (ptr + (idx + j))) needle) := by
        have hm0 := masked_demonic_chunk_eq_pure_slice_window
          k ptr len cur 0 (pow2 k) needle mem (demon step) hfit hlo hhi
        have hsh0 : ∀ x, shrxMask 0 x = x := by
          intro x
          dsimp [shrxMask]
          rw [pow2_zero]
          exact Nat.div_one x
        rw [hsh0] at hm0
        dsimp [bzhiMask] at hm0
        have hltPow := packBits_lt_pow2 (pow2 k)
          (fun i => Nat.beq (demonicReadLane ptr len mem (demon step) cur i) needle)
        have hmodId :
            Nat.mod
              (packBits (pow2 k)
                (fun i => Nat.beq (demonicReadLane ptr len mem (demon step) cur i) needle))
              (pow2 (pow2 k)) =
            packBits (pow2 k)
              (fun i => Nat.beq (demonicReadLane ptr len mem (demon step) cur i) needle) :=
          Nat.mod_eq_of_lt hltPow
        rw [hmodId] at hm0
        rw [hm0]
        apply packBits_congr (pow2 k)
        intro j _
        rw [hcur, Nat.add_assoc]
      rw [hrawEq]
      have hwin := scalarSearchLoop_window_step (pow2 k) (pow2 k) rem idx
        (fun b => Nat.beq b needle) mem ptr (Nat.le_refl (pow2 k)) hWleRem
      dsimp at hwin
      rw [hwin]
      cases hmz : Nat.beq (packBits (pow2 k) (fun j => Nat.beq (mem (ptr + (idx + j))) needle)) 0 with
      | false => rfl
      | true =>
        dsimp
        have hremNextPos : 1 ≤ rem - pow2 k := Nat.sub_pos_of_lt hgtW
        have hfuelNext : rem - pow2 k ≤ f := by
          have hltRem : rem - pow2 k < rem := Nat.sub_lt (Nat.lt_of_lt_of_le (pow2_pos k) hWleRem) (pow2_pos k)
          have hltSucc : rem - pow2 k < f + 1 := Nat.lt_of_lt_of_le hltRem hfuel
          exact Nat.le_of_lt_succ hltSucc
        have hcurNext : cur + pow2 k = ptr + (idx + pow2 k) := by
          rw [hcur, Nat.add_assoc]
        have hsumNext : (idx + pow2 k) + (rem - pow2 k) = len := by
          rw [Nat.add_assoc, Nat.add_sub_of_le hWleRem, hsum]
        have hmodNext : Nat.mod (cur + pow2 k) (pow2 k) = 0 := by
          have h1 : cur + pow2 k = cur + pow2 k * 1 := by rw [Nat.mul_one]
          rw [h1]
          have h2 : Nat.mod (cur + pow2 k * 1) (pow2 k) = Nat.mod cur (pow2 k) :=
            Nat.add_mul_mod_self_left cur (pow2 k) 1
          rw [h2, hmod]
        exact simdAlignedLoopAndEpilog_equiv granuleBits ptr len k needle mem demon hkle
          f (step + 1) (cur + pow2 k) (idx + pow2 k) (rem - pow2 k)
          hfuelNext hremNextPos hcurNext hsumNext hmodNext

theorem lt_of_add_lt_add_left_local : ∀ (a b c : Nat), a + b < a + c → b < c
  | 0, b, c, h => by
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | n + 1, b, c, h => by
    rw [Nat.succ_add, Nat.succ_add] at h
    exact lt_of_add_lt_add_left_local n b c (Nat.lt_of_succ_lt_succ h)

/-- Theorem 14 (Main Theorem — `early_exit_simd_search_equiv`):
    Whenever `k ≤ granuleBits` (`loadSize = 2^k ≤ 2^granuleBits`), the complete
    4-stage aligned-overread SIMD `memchr` (`simdAlignedOverreadSearch`) never
    traps on any `DemonicGranuleLoad`, is completely oblivious to arbitrary
    per-load demonic slack schedules `demon : DemonSched`, and returns the exact
    same `Option Nat` index as byte-by-byte `memchrRef` across all `(ptr, len)`. -/
theorem early_exit_simd_search_equiv
    (granuleBits k needle : Nat)
    (mem : Nat → Nat) (demon : DemonSched)
    (ptr len : Nat)
    (hkle : k ≤ granuleBits) :
    simdAlignedOverreadSearch granuleBits k needle mem demon ptr len =
      IsaSearchOut.ok (memchrRef needle mem ptr len) := by
  dsimp [simdAlignedOverreadSearch, memchrRef]
  cases hlen0 : Nat.beq len 0 with
  | true =>
    have hz : len = 0 := Nat.eq_of_beq_eq_true hlen0
    subst hz
    rfl
  | false =>
    dsimp
    have hlenPos : 1 ≤ len := by
      cases len with
      | zero => cases hlen0
      | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
    let W := pow2 k
    let algn := alignDown k ptr
    let mis := ptr - algn
    let remFirst := W - mis
    have hb := alignDown_bounds k ptr
    have halgn_add_mis : algn + mis = ptr := Nat.add_sub_of_le hb.1
    have hmis_lt_W : mis < W := by
      have hlt : algn + mis < algn + W := by
        rw [halgn_add_mis]
        exact hb.2
      exact lt_of_add_lt_add_left_local algn mis W hlt
    have hmis_le_W : mis ≤ W := Nat.le_of_lt hmis_lt_W
    have hmis_add_remFirst : mis + remFirst = W := Nat.add_sub_of_le hmis_le_W
    have hp_lt_end : ptr < ptr + len := by
      have h0 : ptr + 0 < ptr + len := Nat.add_lt_add_left hlenPos ptr
      rw [Nat.add_zero] at h0
      exact h0
    have hadm0 : granuleLoadAdmissibleBool granuleBits ptr len k algn = true :=
      granuleLoadAdmissibleBool_of_witness granuleBits ptr len k algn ptr
        hkle (alignDown_mod_eq_zero k ptr) hb.1 hb.2 (Nat.le_refl ptr) hp_lt_end
    dsimp [checkedDemonicChunkMask]
    rw [hadm0]
    dsimp
    cases hshort : Nat.ble len remFirst with
    | true =>
      dsimp
      have hlen_le_rf : len ≤ remFirst := Eq.mp Nat.ble_eq hshort
      have hfit : mis + len ≤ W := by
        rw [← hmis_add_remFirst]
        exact Nat.add_le_add_left hlen_le_rf mis
      have hlen_le_W : len ≤ W := Nat.le_trans hlen_le_rf (Nat.sub_le W mis)
      have hlo : ptr ≤ algn + mis := by rw [halgn_add_mis]; exact Nat.le_refl ptr
      have hhi : algn + mis + len ≤ ptr + len := by
        rw [halgn_add_mis]
        exact Nat.le_refl (ptr + len)
      have hm0Eq :
          bzhiMask len
            (shrxMask mis
              (packBits W
                (fun i => Nat.beq (demonicReadLane ptr len mem (demon 0) algn i) needle))) =
            packBits len (fun j => Nat.beq (mem (ptr + (0 + j))) needle) := by
        have hm := masked_demonic_chunk_eq_pure_slice_window
          k ptr len algn mis len needle mem (demon 0) hfit hlo hhi
        rw [hm]
        apply packBits_congr len
        intro j _
        rw [halgn_add_mis, Nat.zero_add]
      change (match Nat.beq (bzhiMask len (shrxMask mis (packBits W (fun i => Nat.beq (demonicReadLane ptr len mem (demon 0) algn i) needle)))) 0 with
        | true => IsaSearchOut.ok none
        | false => IsaSearchOut.ok (some (tzcntW W (bzhiMask len (shrxMask mis (packBits W (fun i => Nat.beq (demonicReadLane ptr len mem (demon 0) algn i) needle))))))) =
        IsaSearchOut.ok (scalarSearchLoop (fun b => Nat.beq b needle) mem ptr len 0)
      rw [hm0Eq]
      have hwin := scalarSearchLoop_window_step W len len 0
        (fun b => Nat.beq b needle) mem ptr hlen_le_W (Nat.le_refl len)
      dsimp at hwin
      rw [hwin, Nat.sub_self, scalarSearchLoop_zero, Nat.zero_add]
      cases Nat.beq (packBits len (fun j => Nat.beq (mem (ptr + (0 + j))) needle)) 0 <;> rfl
    | false =>
      dsimp
      have hgt_rf : remFirst < len := by
        cases Nat.lt_or_ge remFirst len with
        | inl h => exact h
        | inr h =>
          have hc : Nat.ble len remFirst = true := Eq.mpr Nat.ble_eq h
          rw [hc] at hshort; cases hshort
      have hrf_le_len : remFirst ≤ len := Nat.le_of_lt hgt_rf
      have hrf_le_W : remFirst ≤ W := Nat.sub_le W mis
      have hfit : mis + remFirst ≤ W := by
        rw [hmis_add_remFirst]
        exact Nat.le_refl W
      have hlo : ptr ≤ algn + mis := by rw [halgn_add_mis]; exact Nat.le_refl ptr
      have hhi : algn + mis + remFirst ≤ ptr + len := by
        rw [halgn_add_mis]
        exact Nat.add_le_add_left hrf_le_len ptr
      let lanePred := fun i => Nat.beq (demonicReadLane ptr len mem (demon 0) algn i) needle
      have hshiftEq :
          shrxMask mis (packBits W lanePred) =
            packBits remFirst (fun j => Nat.beq (mem (ptr + (0 + j))) needle) := by
        have hm := masked_demonic_chunk_eq_pure_slice_window
          k ptr len algn mis remFirst needle mem (demon 0) hfit hlo hhi
        have hWpack : packBits W lanePred = packBits (mis + remFirst) lanePred :=
          congrArg (fun n => packBits n lanePred) (Eq.symm hmis_add_remFirst)
        have hsh :
            shrxMask mis (packBits W lanePred) =
              packBits remFirst (fun j => lanePred (mis + j)) := by
          rw [hWpack]
          exact shrxMask_packBits mis remFirst lanePred
        have hltPow : shrxMask mis (packBits W lanePred) < pow2 remFirst := by
          rw [hsh]
          exact packBits_lt_pow2 remFirst (fun j => lanePred (mis + j))
        have hmodId :
            bzhiMask remFirst (shrxMask mis (packBits W lanePred)) =
              shrxMask mis (packBits W lanePred) :=
          Nat.mod_eq_of_lt hltPow
        change bzhiMask remFirst (shrxMask mis (packBits W lanePred)) =
          packBits remFirst (fun j => Nat.beq (mem (algn + mis + j)) needle) at hm
        rw [hmodId] at hm
        rw [hm]
        apply packBits_congr remFirst
        intro j _
        rw [halgn_add_mis, Nat.zero_add]
      change (match Nat.beq (shrxMask mis (packBits W lanePred)) 0 with
        | true =>
          simdAlignedLoopAndEpilog granuleBits ptr len k needle mem demon
            (len - remFirst) 1 (algn + W) remFirst (len - remFirst)
        | false => IsaSearchOut.ok (some (tzcntW W (shrxMask mis (packBits W lanePred))))) =
        IsaSearchOut.ok (scalarSearchLoop (fun b => Nat.beq b needle) mem ptr len 0)
      rw [hshiftEq]
      have hwin := scalarSearchLoop_window_step W remFirst len 0
        (fun b => Nat.beq b needle) mem ptr hrf_le_W hrf_le_len
      dsimp at hwin
      rw [hwin, Nat.zero_add]
      cases hsh0 : Nat.beq (packBits remFirst (fun j => Nat.beq (mem (ptr + (0 + j))) needle)) 0 with
      | false =>
        rw [Nat.zero_add]
      | true =>
        dsimp
        have hremAfterPos : 1 ≤ len - remFirst := Nat.sub_pos_of_lt hgt_rf
        have hcur1 : algn + W = ptr + remFirst := by
          rw [← hmis_add_remFirst, ← Nat.add_assoc, halgn_add_mis]
        have hsum1 : remFirst + (len - remFirst) = len := Nat.add_sub_of_le hrf_le_len
        have hmod1 : Nat.mod (algn + W) W = 0 := by
          have hw1 : algn + W = algn + W * 1 := by rw [Nat.mul_one]
          rw [hw1]
          have hw2 : Nat.mod (algn + W * 1) W = Nat.mod algn W :=
            Nat.add_mul_mod_self_left algn W 1
          rw [hw2]
          exact alignDown_mod_eq_zero k ptr
        exact simdAlignedLoopAndEpilog_equiv granuleBits ptr len k needle mem demon hkle
          (len - remFirst) 1 (algn + W) remFirst (len - remFirst)
          (Nat.le_refl _) hremAfterPos hcur1 hsum1 hmod1

/-- Corollary 15 (`TotalMirAsmDemonicEquiv` Lifting for Exported Safe `memchr`):
    Embeds `memchrRef` and `simdAlignedOverreadSearch` into `MirOut`/`IsaOut` and
    establishes total panic-exact, demonic-slack-oblivious cross-level equivalence. -/
def memchrMirSpec (needle : Nat) (mem : Nat → Nat) (q : Nat × Nat) : MirOut (Option Nat) Unit :=
  MirOut.returned (memchrRef needle mem q.1 q.2) ()

def memchrIsaImpl (granuleBits k needle : Nat) (mem : Nat → Nat)
    (q : Nat × Nat) (d : DemonSched) : IsaOut (Option Nat) Unit :=
  match simdAlignedOverreadSearch granuleBits k needle mem d q.1 q.2 with
  | IsaSearchOut.ok res => IsaOut.halted res ()
  | IsaSearchOut.trap => IsaOut.trap

theorem simd_overread_memchr_total_demonic_equiv
    (granuleBits k needle : Nat) (mem : Nat → Nat) (hkle : k ≤ granuleBits) :
    TotalMirAsmDemonicEquiv
      (memchrMirSpec needle mem)
      (memchrIsaImpl granuleBits k needle mem) := by
  intro q d
  dsimp [memchrMirSpec, memchrIsaImpl]
  rw [early_exit_simd_search_equiv granuleBits k needle mem d q.1 q.2 hkle]
  dsimp
  apply And.intro (fun h => by cases h)
  apply And.intro (fun h => by cases h)
  apply And.intro
  · intro v m
    exact Iff.intro
      (fun h => by injection h with hv hm; subst hv; subst hm; rfl)
      (fun h => by injection h with hv hm; subst hv; subst hm; rfl)
  · apply And.intro
    · intro m
      exact Iff.intro (fun h => by cases h) (fun h => by cases h)
    · exact Iff.intro (fun h => by cases h) (fun h => by cases h)

end AlignedSimdOverread
