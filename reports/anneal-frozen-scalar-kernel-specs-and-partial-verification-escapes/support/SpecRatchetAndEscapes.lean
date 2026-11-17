-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Standalone Lean 4.34.1 probe: Frozen scalar kernel grounding ratchets, `DefIndex`-invariant enum resolution, and partial-verification boundary escapes

Self-contained (Lean core `Init` only; zero external imports, zero `sorry`, zero
`native_decide`). Pinned toolchain: `leanprover/lean4` `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`).

Sections:
1. `DefIndex`-invariant locals-type lookup for enum parameters (`resolveArg0EnumVal`)
   so renumbering `DefId` / `EnumTy.id` slots across helper additions does not
   break verified specifications.
2. Wire-format collusion (`CoupledRoundTrip`), stored-block compression-ratio
   collapse, uninformative totality, and the `pickSmaller` reference-stream
   size arbitrator (`LockedRoundTrip`).
3. Partial-verification boundary escapes:
   - `find_match` `256`-vs-`258` tail overrun and repaired `matchTailBoundNat`;
   - Literal-prefixed wild-copy margin violations (`3 + 264 = 267 > 266` and
     `4 + 288 = 292 > 290 <= 304`);
   - Observational prefix refinement (`ObsSlicePrefixEquiv`), out-of-capacity
     non-absorption, `MaybeUninit` 8-byte lookback initialization (`dist >= 8`),
     logical `out_max` vs. physical `buf.len` separation, and wrapping 32 KiB
     ring-buffer history clobbering on distances in `(R - W, R]`.
4. `#print axioms` receipts pinning the exact axiom footprint of every theorem.
-/

namespace FrozenKernelEscapes

/-! ## 1. `DefIndex`-invariant locals-type enum resolution -/

section DefIndexInvariance

structure EnumTy where
  id : Nat
  discriminants : List Nat
  deriving DecidableEq, Repr

inductive Ty where
  | scalar (bits : Nat)
  | enum (ety : EnumTy)
  deriving DecidableEq, Repr

inductive Val where
  | unit
  | enumVal (ety : EnumTy) (variantIdx : Nat)
  deriving DecidableEq, Repr

structure Body where
  locals : List Ty
  deriving Repr

/-- Inspect `locals[1]` directly from the captured body's `locals` list rather
than hardcoding an external `adt.did().index.as_u32()` constant. -/
def resolveArg0EnumVal (body : Body) (variantIdx : Nat) : Val :=
  match body.locals with
  | _ :: .enum ety :: _ => .enumVal ety variantIdx
  | _ => .unit

/-- Evaluating a 35-variant failure predicate on a resolved enum value depends
only on the normalized discriminant / variant index (`idx >= 25`), never on
`EnumTy.id` assigned by `rustc`'s crate-local `DefIndex`. -/
def evalEnumFailureAt (val : Val) : Bool :=
  match val with
  | .enumVal _ idx => decide (idx >= 25)
  | .unit => false

theorem resolveArg0EnumVal_defIndex_invariant
    (retTy : Ty) (discrs : List Nat) (id1 id2 variantIdx : Nat) :
    let body1 : Body := ⟨[retTy, .enum ⟨id1, discrs⟩]⟩
    let body2 : Body := ⟨[retTy, .enum ⟨id2, discrs⟩]⟩
    evalEnumFailureAt (resolveArg0EnumVal body1 variantIdx) =
      evalEnumFailureAt (resolveArg0EnumVal body2 variantIdx) := by
  rfl

/-- Contrast: a brittle specification that pins a constant `expectedId` breaks
as soon as adding a helper item shifts `adt.did().index.as_u32()` (`7 -> 42`). -/
def brittleEnumCheck (expectedId : Nat) (val : Val) : Bool :=
  match val with
  | .enumVal ety idx => ety.id == expectedId && decide (idx >= 25)
  | .unit => false

theorem brittleEnumCheck_breaks_on_defIndex_shift :
    let bodyShifted : Body := ⟨[.scalar 8, .enum ⟨42, [0, 1]⟩]⟩
    brittleEnumCheck 7 (resolveArg0EnumVal bodyShifted 30) = false ∧
    evalEnumFailureAt (resolveArg0EnumVal bodyShifted 30) = true := by
  decide

end DefIndexInvariance

/-! ## 2. Encoder/decoder collusion, stored collapse, and `pickSmaller` ratchets -/

section Ratchets

/-- Toy locked reference format: tag `0` is a raw stored payload; tag `1`
followed by `[b, n]` decodes to `n` copies of byte `b`. -/
def refDecode : List UInt8 → Option (List UInt8)
  | [] => none
  | h :: rest =>
    if h = 0 then some rest
    else if h = 1 then
      match rest with
      | [b, n] => some (List.replicate n.toNat b)
      | _ => none
    else none

/-- Candidate encoder coupled with a candidate decoder: satisfies self round-trip
even when neither side uses the locked wire format. -/
def CoupledRoundTrip (enc : List UInt8 → List UInt8)
    (dec : List UInt8 → Option (List UInt8)) : Prop :=
  ∀ d, dec (enc d) = some d

/-- Grounded round-trip through the locked reference decoder. -/
def LockedRoundTrip (enc : List UInt8 → List UInt8) : Prop :=
  ∀ d, refDecode (enc d) = some d

theorem collusion_passes_coupled : CoupledRoundTrip id some := fun _ => rfl

theorem collusion_fails_locked : ¬ LockedRoundTrip id := by
  intro h
  have h5 := h [5]
  revert h5
  decide

theorem stored_passes_locked : LockedRoundTrip (fun d => 0 :: d) := fun _ => rfl

theorem stored_ratio_collapse :
    refDecode [1, 7, 5] = some (List.replicate 5 7) ∧
    ([1, 7, 5] : List UInt8).length = 3 ∧
    ((0 : UInt8) :: List.replicate 5 7).length = 6 := by
  decide

theorem totality_unconstraining :
    (∀ d : List UInt8, ∃ out, (fun _ => ([] : List UInt8)) d = out) ∧
    ¬ LockedRoundTrip (fun _ => []) := by
  refine ⟨fun d => ⟨_, rfl⟩, ?_⟩
  intro h
  have h0 := h []
  revert h0
  decide

/-- Reference-stream size arbitrator: picks `optStream` iff it is no larger
than `refStream`, preserving any stream-level validity predicate (`ValidStream`). -/
def pickSmaller (optStream refStream : List UInt8) : List UInt8 :=
  if optStream.length ≤ refStream.length then optStream else refStream

def PickSmallerRatchetClaim : Prop :=
  ∀ (ValidStream : List UInt8 → Prop) (optStream refStream : List UInt8),
    ValidStream optStream → ValidStream refStream →
    ValidStream (pickSmaller optStream refStream) ∧
    (pickSmaller optStream refStream).length ≤ refStream.length

theorem pickSmaller_valid_and_no_larger : PickSmallerRatchetClaim := by
  intro ValidStream optStream refStream h_opt h_ref
  unfold pickSmaller
  split
  · rename_i h_le
    exact ⟨h_opt, h_le⟩
  · exact ⟨h_ref, Nat.le_refl _⟩

theorem pickSmaller_blocks_stored_collapse :
    pickSmaller ((0 : UInt8) :: List.replicate 5 7) [1, 7, 5] = [1, 7, 5] := by
  decide

end Ratchets

/-! ## 3. Partial-verification boundary escapes -/

section Escapes

/-! ### 3.1 `find_match` `256`-byte comparison vs. `258`-byte reported length -/

theorem findMatch_compared_bytes : 8 + 31 * 8 = 256 ∧ 2 + 32 * 8 = 258 := by decide

theorem findMatch_256_prefix_violates_full_match_258
    (p : List UInt8) (h_len : p.length = 256) :
    let wA := p ++ [10, 20]
    let wB := p ++ [99, 20]
    wA.length = 258 ∧ wB.length = 258 ∧ wA.take 256 = wB.take 256 ∧ wA ≠ wB := by
  dsimp only
  refine ⟨by simp [List.length_append, h_len], by simp [List.length_append, h_len], ?_, ?_⟩
  · rw [← h_len, List.take_left, List.take_left]
  · intro h_eq
    have h_drop : (p ++ [10, 20]).drop p.length = (p ++ [99, 20]).drop p.length :=
      congrArg (List.drop p.length) h_eq
    rw [List.drop_left, List.drop_left] at h_drop
    revert h_drop
    decide

theorem findMatch_256_plus_tail2_sound (a b : List UInt8)
    (h_eq256 : a.take 256 = b.take 256) (h_tail2 : a.drop 256 = b.drop 256) : a = b := by
  rw [← List.take_append_drop 256 a, ← List.take_append_drop 256 b, h_eq256, h_tail2]

/-- Repaired scalar comparison-length bound matching bytes up to RFC 1951 max 258. -/
def matchTailBoundNat (p1 p2 inputLen : Nat) : Nat :=
  let hi := if p1 ≥ p2 then p1 else p2
  if hi ≥ inputLen then 0
  else
    let rem := inputLen - hi
    if rem ≥ 258 then 258 else rem

def MatchTailBoundSoundnessClaim : Prop :=
  (∀ p1 p2 inputLen : Nat, p1 ≤ inputLen → p2 ≤ inputLen →
    let ret := matchTailBoundNat p1 p2 inputLen
    p1 + ret ≤ inputLen ∧ p2 + ret ≤ inputLen ∧ ret ≤ 258) ∧
  (∀ p1 p2 inputLen : Nat, (p1 ≥ inputLen ∨ p2 ≥ inputLen) →
    matchTailBoundNat p1 p2 inputLen = 0)

theorem matchTailBound_sound : MatchTailBoundSoundnessClaim := by
  refine ⟨?_, ?_⟩
  · intro p1 p2 n h1 h2
    unfold matchTailBoundNat
    by_cases hp : p1 ≥ p2
    · simp only [hp, ite_true]
      by_cases hn : p1 ≥ n
      · simp only [hn, ite_true]; omega
      · simp only [hn, ite_false]
        by_cases hr : n - p1 ≥ 258
        · simp only [hr, ite_true]; omega
        · simp only [hr, ite_false]; omega
    · simp only [hp, ite_false]
      by_cases hn : p2 ≥ n
      · simp only [hn, ite_true]; omega
      · simp only [hn, ite_false]
        by_cases hr : n - p2 ≥ 258
        · simp only [hr, ite_true]; omega
        · simp only [hr, ite_false]; omega
  · intro p1 p2 n h
    unfold matchTailBoundNat
    by_cases hp : p1 ≥ p2
    · simp only [hp, ite_true]
      have hn : p1 ≥ n := by omega
      simp only [hn, ite_true]
    · simp only [hp, ite_false]
      have hn : p2 ≥ n := by omega
      simp only [hn, ite_true]

/-! ### 3.2 Literal-prefixed wild-copy margin violations (`267 > 266` and `292 > 290 <= 304`) -/

/-- Bytes touched past the fast-loop iteration start pointer by `lLit` fused
literal bytes followed by a `w`-byte-stride copy of a `matchLen`-byte match. -/
def wildCopyTouchedBytes (lLit matchLen w : Nat) : Nat :=
  lLit + ((matchLen + w - 1) / w) * w

theorem wildCopy_margin_266_violated :
    wildCopyTouchedBytes 0 258 8 = 264 ∧ wildCopyTouchedBytes 0 258 8 ≤ 266 ∧
    3 + 264 = 267 ∧ wildCopyTouchedBytes 3 258 8 = 267 ∧
    266 < wildCopyTouchedBytes 3 258 8 := by
  decide

theorem simd_guard_290_vs_292 :
    258 + 32 = 290 ∧ wildCopyTouchedBytes 4 258 32 = 292 ∧
    290 < wildCopyTouchedBytes 4 258 32 ∧ wildCopyTouchedBytes 4 258 32 ≤ 304 ∧
    wildCopyTouchedBytes 4 258 16 = 276 := by
  decide

/-! ### 3.3 Observational slice-prefix refinement vs. physical capacity & `out_max` separation -/

/-- Observational prefix equivalence: equal total slice length and equal live
prefix `[0, written)`, absorbing uninitialized / slack writes within capacity. -/
def ObsSlicePrefixEquiv (written : Nat) (buf1 buf2 : List UInt8) : Prop :=
  buf1.length = buf2.length ∧ buf1.take written = buf2.take written

def safeMatchOut (activePrefix slackOld : List UInt8) : List UInt8 := activePrefix ++ slackOld
def wildMatchOut (activePrefix slackWild : List UInt8) : List UInt8 := activePrefix ++ slackWild

theorem wildMatch_satisfies_prefix_equiv (activePrefix slackOld slackWild : List UInt8)
    (h_slack_len : slackWild.length = slackOld.length) :
    ObsSlicePrefixEquiv activePrefix.length
      (wildMatchOut activePrefix slackWild) (safeMatchOut activePrefix slackOld) := by
  unfold ObsSlicePrefixEquiv wildMatchOut safeMatchOut
  constructor
  · simp [List.length_append, h_slack_len]
  · rw [List.take_left, List.take_left]

theorem wildMatch_violates_bit_exact :
    wildMatchOut [1, 2, 3, 4, 5] [99, 99, 99, 99, 99] ≠
      safeMatchOut [1, 2, 3, 4, 5] [0, 0, 0, 0, 0] := by
  decide

theorem oob_write_not_absorbed (buf extra : List UInt8) (k : Nat)
    (h : ObsSlicePrefixEquiv k (buf ++ extra) buf) : extra = [] := by
  have hl := h.1
  rw [List.length_append] at hl
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Logical vs. physical slack separation: a scalar check `out_pos + guard <= out_max`
only implies `out_pos + touched <= dst_len` when `out_max <= dst_len` and `guard >= touched`. -/
theorem scalar_guard_insufficient_without_coupling :
    let outPos := 100
    let guard := 290
    let touched := 292
    let outMax := 394
    let dstLen := 391
    outPos + guard ≤ outMax ∧ dstLen < outPos + touched := by
  decide

/-- Reading 8 bytes at `outPos - dist` stays within `[0, outPos)` iff `dist >= 8`. -/
theorem wildCopy_8byte_read_strictly_initialized_iff (outPos dist : Nat) (h_le : dist ≤ outPos) :
    (outPos - dist) + 7 < outPos ↔ 8 ≤ dist := by
  omega

/-! ### 3.4 Wrapping 32 KiB ring buffer overshoot clobbering distances in `(R - W, R]` -/

def wildOvershoot (matchLen w : Nat) : Nat := ((matchLen + w - 1) / w) * w - matchLen

theorem wildOvershoot_lt (matchLen w : Nat) (hw : 0 < w) : wildOvershoot matchLen w < w := by
  have h := Nat.div_mul_le_self (matchLen + w - 1) w
  unfold wildOvershoot
  omega

theorem ring_clobber_distance (R w matchLen j : Nat) (hw : 0 < w) (hwR : w ≤ R)
    (hj : j < wildOvershoot matchLen w) : R - w < R - j ∧ R - j ≤ R := by
  have := wildOvershoot_lt matchLen w hw
  omega

theorem ring_32768_instances :
    wildOvershoot 3 8 = 5 ∧ (∀ j, j < 5 → 32768 - 8 < 32768 - j) ∧
    wildOvershoot 258 8 = 6 ∧ wildOvershoot 3 32 = 29 ∧
    (∀ j, j < 29 → 32768 - 32 < 32768 - j) := by
  decide

def ringCopy (ring : List Nat) (head dist n : Nat) : List Nat :=
  (List.range n).foldl
    (fun r k => r.set ((head + k) % r.length) (r.getD ((head + k + r.length - dist) % r.length) 0))
    ring

theorem ring16_wild_clobbers_distance_R :
    (ringCopy (List.range 16) 0 8 3).getD 3 0 = 3 ∧
    (ringCopy (List.range 16) 0 8 8).getD 3 0 = 11 ∧
    16 - 8 < 16 := by
  decide

end Escapes

/-! ## 4. Axiom receipts -/

section Receipts

/-- info: 'FrozenKernelEscapes.resolveArg0EnumVal_defIndex_invariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms resolveArg0EnumVal_defIndex_invariant
/-- info: 'FrozenKernelEscapes.brittleEnumCheck_breaks_on_defIndex_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms brittleEnumCheck_breaks_on_defIndex_shift
/-- info: 'FrozenKernelEscapes.collusion_passes_coupled' does not depend on any axioms -/
#guard_msgs in #print axioms collusion_passes_coupled
/-- info: 'FrozenKernelEscapes.collusion_fails_locked' depends on axioms: [propext] -/
#guard_msgs in #print axioms collusion_fails_locked
/-- info: 'FrozenKernelEscapes.stored_passes_locked' depends on axioms: [propext] -/
#guard_msgs in #print axioms stored_passes_locked
/-- info: 'FrozenKernelEscapes.stored_ratio_collapse' depends on axioms: [propext] -/
#guard_msgs in #print axioms stored_ratio_collapse
/-- info: 'FrozenKernelEscapes.totality_unconstraining' depends on axioms: [propext] -/
#guard_msgs in #print axioms totality_unconstraining
/-- info: 'FrozenKernelEscapes.pickSmaller_valid_and_no_larger' does not depend on any axioms -/
#guard_msgs in #print axioms pickSmaller_valid_and_no_larger
/-- info: 'FrozenKernelEscapes.pickSmaller_blocks_stored_collapse' does not depend on any axioms -/
#guard_msgs in #print axioms pickSmaller_blocks_stored_collapse
/-- info: 'FrozenKernelEscapes.findMatch_256_prefix_violates_full_match_258' depends on axioms: [propext] -/
#guard_msgs in #print axioms findMatch_256_prefix_violates_full_match_258
/-- info: 'FrozenKernelEscapes.findMatch_256_plus_tail2_sound' does not depend on any axioms -/
#guard_msgs in #print axioms findMatch_256_plus_tail2_sound
/-- info: 'FrozenKernelEscapes.matchTailBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms matchTailBound_sound
/-- info: 'FrozenKernelEscapes.wildCopy_margin_266_violated' does not depend on any axioms -/
#guard_msgs in #print axioms wildCopy_margin_266_violated
/-- info: 'FrozenKernelEscapes.simd_guard_290_vs_292' does not depend on any axioms -/
#guard_msgs in #print axioms simd_guard_290_vs_292
/-- info: 'FrozenKernelEscapes.wildMatch_satisfies_prefix_equiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms wildMatch_satisfies_prefix_equiv
/-- info: 'FrozenKernelEscapes.wildMatch_violates_bit_exact' does not depend on any axioms -/
#guard_msgs in #print axioms wildMatch_violates_bit_exact
/-- info: 'FrozenKernelEscapes.oob_write_not_absorbed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms oob_write_not_absorbed
/-- info: 'FrozenKernelEscapes.scalar_guard_insufficient_without_coupling' does not depend on any axioms -/
#guard_msgs in #print axioms scalar_guard_insufficient_without_coupling
/--
info: 'FrozenKernelEscapes.wildCopy_8byte_read_strictly_initialized_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms wildCopy_8byte_read_strictly_initialized_iff
/-- info: 'FrozenKernelEscapes.wildOvershoot_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wildOvershoot_lt
/-- info: 'FrozenKernelEscapes.ring_clobber_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ring_clobber_distance
/-- info: 'FrozenKernelEscapes.ring_32768_instances' does not depend on any axioms -/
#guard_msgs in #print axioms ring_32768_instances
/-- info: 'FrozenKernelEscapes.ring16_wild_clobbers_distance_R' depends on axioms: [propext] -/
#guard_msgs in #print axioms ring16_wild_clobbers_distance_R

end Receipts

end FrozenKernelEscapes
