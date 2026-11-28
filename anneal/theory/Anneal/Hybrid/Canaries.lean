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
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Anneal.InitLemmas
public import Anneal.Framework
public import Anneal.Hybrid

public section

/-!
# Canaries for `Anneal.Hybrid`

Concrete instances of every combinator in `Anneal.Hybrid`, together with
the counterexamples that motivate its design:

1. **Portfolios:** choosing the first producer that returns any candidate
   and only then checking it loses a valid backup
   (`naive_precheck_orelse_drops_valid_backup`); `firstAccepted` skips an
   oversized witness and a wrong candidate (`canary_portfolio`).
2. **Fallbacks:** re-checking the fallback's result with an incomplete
   checker aborts on an input where the fallback is correct
   (`runtime_checked_fallback_aborts`), while `withFallback` stays sound.
3. **Hint steps and streams:** a rejected hint falls back to the current
   state (`canary_hint_steps`), and a stream stops at the first rejected
   chunk without emitting it (`canary_stream_prefix`).
4. **Certificate cuts:** `Anneal.LinearArith` natural-number and integer
   cut certificates and an `Anneal.BitTrieLrat` refutation discharge their
   goals by `rfl` through `certGateCut_sound`; an oversized or forged
   certificate is rejected.
5. **`zerocopy` slice-DST casts (`sliceDstCastGate`):** a witness-free
   relational gate for the result of zerocopy's
   `DstLayout::validate_cast_and_convert_metadata`
   (`zerocopy/src/layout.rs`): the element count and split point must fit,
   be aligned, and be maximal. The object's pointer alignment and its
   size-rounding alignment are separate, as in zerocopy, where a
   `repr(packed)` wrapper lowers the first but not the second. The gate is
   proved sound, accepts the maximal candidate, and rejects a sub-maximal
   one and a misaligned suffix cast. The model works over unbounded `Nat`
   with a `usize` bound on `addr + bytes_len`; it is not a proof about the
   Rust function.
6. **In-process producers:** a producer free of undefined behavior that
   overwrites caller memory before returning a wrong candidate breaks the
   composed contract even with a sound checker and a correct fallback
   (`rung15_without_callerMemPreserved_unsound`); a memory-preserving
   producer with the same wrong candidate does not
   (`canary_rung15_preserving`).
7. **Anti-vacuity:** an always-`none` body has no accepted witness, and an
   accepting body does (`canary_hasAcceptedWitness`); the slice-DST gate's
   specification kills a mutant inside the accepted fibre
   (`canary_dst_accepted_dichotomy`).
8. **Ratchets:** a two-producer portfolio with stronger effect guarantees
   may replace a single producer and returns the same output
   (`canary_ratchet`), and a caller's proof carries over
   (`canary_ratchet_outer`).
9. **Bridges:** `maskLe` is `Anneal.Framework.effectMaskLe`
   (`maskLe_eq_effectMaskLe`).
-/

namespace Anneal.Hybrid.Canaries

open Trusted.Framework Anneal.Hybrid

/-! ## Portfolios -/

/-- Accepts exactly `y = x`. -/
@[expose] def eqGate : CertifiedGate Nat Nat Unit (fun _ => True)
    (fun x y => y = x) :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun x y _ => Nat.beq y x
    sound := fun _ _ _ _ _ h => Nat.eq_of_beq_eq_true h }

/-- Take the first producer that returns any candidate, before checking. -/
@[expose] def naivePreGateChoice {E Y W : Type} (rs : List (RawOutcome E Y W)) :
    RawOutcome E Y W :=
  List.foldr
    (fun r acc =>
      match r with
      | .candidate y w => .candidate y w
      | _ => acc)
    .trapped rs

/-- A wrong candidate followed by the right one. -/
@[expose] def twoCandidates : List (RawOutcome Unit Nat Unit) :=
  [.candidate 999 (), .candidate 7 ()]

/-- Choosing before checking loses the valid second candidate, while
`firstAccepted` finds it. -/
theorem naive_precheck_orelse_drops_valid_backup :
    evalGate eqGate 7 (naivePreGateChoice twoCandidates) =
      .error .rejectedByChecker ∧
    firstAccepted eqGate 7 twoCandidates = .ok 7 :=
  ⟨rfl, rfl⟩

/-- Accepts `y = x + 1` with a witness of at most four elements. -/
@[expose] def succGate : CertifiedGate Nat Nat (List Nat) (fun _ => True)
    (fun x y => y = x + 1) :=
  { maxWitness := fun _ => 4
    wSize := List.length
    check := fun x y _ => Nat.beq y (x + 1)
    sound := fun _ _ _ _ _ h => Nat.eq_of_beq_eq_true h }

/-- An oversized witness, a wrong candidate, and a trap are skipped. -/
theorem canary_portfolio :
    firstAccepted succGate 10
        ([.candidate 11 [0, 0, 0, 0, 0], .candidate 999 [], .trapped,
          .candidate 11 [1, 2]] : List (RawOutcome Unit Nat (List Nat)))
      = .ok 11 ∧
    evalGate (E := Unit) succGate 10 (.candidate 11 [0, 0, 0, 0, 0]) =
      .error (.witnessOversized 5 4) ∧
    firstAccepted succGate 10
        ([.candidate 999 [], .prodErr ()] :
          List (RawOutcome Unit Nat (List Nat))) =
      .error (.producerFailed ()) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Fallbacks -/

/-- Sound for `x ≤ y` but accepts only `y = x + 1`. -/
@[expose] def strictSuccGate : CertifiedGate Nat Nat Unit (fun _ => True)
    (fun x y => x ≤ y) :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun x y _ => Nat.beq y (x + 1)
    sound := fun x _ _ _ _ h => by
      rw [Nat.eq_of_beq_eq_true h]
      exact Nat.le_succ x }

/-- Use the fallback only if the checker accepts it, aborting (`none`)
otherwise. -/
@[expose] def assertCheckedFallback {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (res : Except (HybridErr E) Y) (fb : X → Y × W) : Option Y :=
  match res with
  | .ok y => some y
  | .error _ =>
    match g.check x (fb x).1 (fb x).2 with
    | true => some (fb x).1
    | false => none

/-- The identity fallback is correct for `x ≤ y`, but the checker does not
accept it, so re-checking aborts. `withFallback` returns it and is sound
for every producer outcome. -/
theorem runtime_checked_fallback_aborts :
    (∀ x : Nat, x ≤ x) ∧
    assertCheckedFallback strictSuccGate 5
        (.error (HybridErr.producerTrapped : HybridErr Unit))
        (fun x => (x, ())) = none ∧
    (∀ raw : RawOutcome Unit Nat Unit,
      5 ≤ withFallback 5 (evalGate strictSuccGate 5 raw) (fun x => x)) :=
  ⟨Nat.le_refl, rfl, fun raw =>
    withFallback_total_sound strictSuccGate 5 raw (fun x => x) True.intro
      (fun x _ => Nat.le_refl x)⟩

/-! ## Hint steps and streams -/

/-- Accepts a next state that is at most `100` and does not decrease. -/
@[expose] def boundedStepGate : CertifiedGate (Nat × Nat) Nat Unit
    (fun su => su.1 ≤ 100) (fun su s' => s' ≤ 100 ∧ su.1 ≤ s') :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun su s' _ => Nat.ble s' 100 && Nat.ble su.1 s'
    sound := fun _ _ _ _ _ h =>
      ⟨Nat.le_of_ble_eq_true (Anneal.InitLemmas.bool_and_left h),
        Nat.le_of_ble_eq_true (Anneal.InitLemmas.bool_and_right h)⟩ }

/-- The hint `70` would overshoot, so the state stays at `60`. -/
theorem canary_hint_steps :
    foldHintSteps (Inv := fun s => s ≤ 100) (StepRel := fun s _ s' => s ≤ s')
        boundedStepGate
        (fun s u => (.candidate (s + u) () : RawOutcome Unit Nat Unit))
        (fun su => su.1) 0 [10, 50, 70, 5] = 65 ∧
    ∀ us : List Nat,
      foldHintSteps (Inv := fun s => s ≤ 100)
        (StepRel := fun s _ s' => s ≤ s') boundedStepGate
        (fun s u => (.candidate (s + u) () : RawOutcome Unit Nat Unit))
        (fun su => su.1) 0 us ≤ 100 :=
  ⟨rfl, fun us =>
    foldHintSteps_preserves_inv (Inv := fun s => s ≤ 100)
      (StepRel := fun s _ s' => s ≤ s') boundedStepGate _ (fun su => su.1)
      (fun _ h => ⟨h, Nat.le_refl _⟩) us 0 (Nat.zero_le _)⟩

/-- Accepts a chunk below `100` that does not decrease, and makes it the
new state. -/
@[expose] def monotoneChunkGate : CertifiedGate (Nat × Nat) (Nat × Nat) Unit
    (fun su => su.1 < 100) (fun _ sc => sc.1 < 100 ∧ sc.2 < 100) :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun su sc _ =>
      Nat.ble su.1 sc.2 && Nat.ble (sc.2 + 1) 100 && Nat.beq sc.1 sc.2
    sound := fun _ sc _ _ _ h => by
      have hEq := Nat.eq_of_beq_eq_true (Anneal.InitLemmas.bool_and_right h)
      have hLt : sc.2 < 100 := Nat.le_of_ble_eq_true
        (Anneal.InitLemmas.bool_and_right (Anneal.InitLemmas.bool_and_left h))
      refine ⟨?_, hLt⟩
      rw [hEq]
      exact hLt }

/-- `500` is rejected, so `30` is never considered. -/
theorem canary_stream_prefix :
    foldStreamPrefix (AccInv := fun s => s < 100)
        (ValidChunk := fun c => c < 100)
        monotoneChunkGate
        (fun _ u => (.candidate (u, u) () : RawOutcome Unit (Nat × Nat) Unit))
        0 [10, 25, 500, 30] =
      ([10, 25], some .rejectedByChecker) :=
  rfl

/-! ## Certificate cuts -/

/-- `2 * i + 1 ≤ 2 * n → i < n` from the existing Farkas certificate,
through the gate. -/
theorem canary_natCut_parity (i n : Nat) (h : 2 * i + 1 ≤ 2 * n) : i < n :=
  certGateCut_sound (natCutGate 8) (x := Anneal.LinearArith.parityStrideGoal)
    (y := ()) (w := Anneal.LinearArith.parityStrideFarkasCert) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl) [i, n] h

/-- The four-step certificate is rejected under a two-step bound and
accepted under an eight-step bound; a truncated certificate is rejected by
the checker. -/
theorem canary_natCut_bounds :
    evalGate (E := Unit) (natCutGate 2) Anneal.LinearArith.parityStrideGoal
        (.candidate () Anneal.LinearArith.parityStrideCert) =
      .error (.witnessOversized 4 2) ∧
    evalGate (E := Unit) (natCutGate 8) Anneal.LinearArith.parityStrideGoal
        (.candidate () Anneal.LinearArith.parityStrideCert) = .ok () ∧
    evalGate (E := Unit) (natCutGate 8) Anneal.LinearArith.parityStrideGoal
        (.candidate () [.hyp 0]) = .error .rejectedByChecker :=
  ⟨rfl, rfl, rfl⟩

/-- An LRAT refutation checked through the gate. -/
theorem canary_rup_unsat :
    Anneal.BitTrieLrat.UnsatCnf Anneal.BitTrieLrat.sampleUnsatCnf :=
  certGateCut_sound (rupGate 6 8) (y := ())
    (w := Anneal.BitTrieLrat.sampleUnsatSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- A hint chain that ends without a conflict is rejected. -/
theorem canary_rup_forged_rejected :
    evalGate (E := Unit) (rupGate 6 8) Anneal.BitTrieLrat.sampleUnsatCnf
        (.candidate ()
          [.addRup 5 [Anneal.BitTrieLrat.mkLit 3 true] [0]]) =
      .error .rejectedByChecker :=
  rfl

/-! ## `zerocopy` slice-DST casts -/

/-- The inputs of `DstLayout::validate_cast_and_convert_metadata` for a
slice DST: the address and length of the source bytes, the object's pointer
alignment (`DstLayout::align`), the trailing-slice layout (`sizeBase`,
`phase`, `elemSize`, and the size-rounding alignment `sizeAlign`), and the
cast direction. -/
structure DstCastInput where
  addr : Nat
  bytesLen : Nat
  align : Nat
  sizeBase : Nat
  phase : Nat
  elemSize : Nat
  sizeAlign : Nat
  isPrefix : Bool

/-- `v` rounded up to a multiple of `a` (for `0 < a`). -/
@[expose] def roundUpNat (v a : Nat) : Nat :=
  match Nat.beq (Nat.mod v a) 0 with
  | true => v
  | false => v + (a - Nat.mod v a)

/-- Size of the slice DST with `elems` trailing elements. -/
@[expose] def dstObjectSize (x : DstCastInput) (elems : Nat) : Nat :=
  x.sizeBase + roundUpNat (x.phase + elems * x.elemSize) x.sizeAlign

/-- `usize::MAX` on 64-bit targets. -/
@[expose] def usizeMax : Nat := 18446744073709551615

/-- Where the source bytes are split for an object of `selfBytes` bytes. -/
@[expose] def dstSplitAt (x : DstCastInput) (selfBytes : Nat) : Nat :=
  match x.isPrefix with
  | true => selfBytes
  | false => x.bytesLen - selfBytes

/-- Address of the cast object. -/
@[expose] def dstTargetAddr (x : DstCastInput) (splitAt : Nat) : Nat :=
  match x.isPrefix with
  | true => x.addr
  | false => x.addr + splitAt

/-- `(elems, splitAt)` is a valid result: the object fits, the split point
matches it, the object is aligned, and one more element would not fit. -/
@[expose] def ValidDstCast (x : DstCastInput) (out : Nat × Nat) : Prop :=
  0 < x.align ∧ 0 < x.sizeAlign ∧ 0 < x.elemSize ∧
  x.addr + x.bytesLen ≤ usizeMax ∧
  dstObjectSize x out.1 ≤ x.bytesLen ∧
  out.2 = dstSplitAt x (dstObjectSize x out.1) ∧
  Nat.mod (dstTargetAddr x out.2) x.align = 0 ∧
  x.bytesLen < dstObjectSize x (out.1 + 1)

/-- Boolean check of `ValidDstCast`, recomputing every size from the
layout rather than trusting the candidate. -/
@[expose] def checkDstCast (x : DstCastInput) (out : Nat × Nat) : Bool :=
  Nat.ble 1 x.align && Nat.ble 1 x.sizeAlign && Nat.ble 1 x.elemSize &&
    Nat.ble (x.addr + x.bytesLen) usizeMax &&
    Nat.ble (dstObjectSize x out.1) x.bytesLen &&
    Nat.beq out.2 (dstSplitAt x (dstObjectSize x out.1)) &&
    Nat.beq (Nat.mod (dstTargetAddr x out.2) x.align) 0 &&
    Nat.ble (x.bytesLen + 1) (dstObjectSize x (out.1 + 1))

theorem checkDstCast_sound (x : DstCastInput) (out : Nat × Nat)
    (h : checkDstCast x out = true) : ValidDstCast x out := by
  have h6 := Anneal.InitLemmas.bool_and_right h
  have r5 := Anneal.InitLemmas.bool_and_left h
  have h5 := Anneal.InitLemmas.bool_and_right r5
  have r4 := Anneal.InitLemmas.bool_and_left r5
  have h4 := Anneal.InitLemmas.bool_and_right r4
  have r3 := Anneal.InitLemmas.bool_and_left r4
  have h3 := Anneal.InitLemmas.bool_and_right r3
  have r2 := Anneal.InitLemmas.bool_and_left r3
  have h2 := Anneal.InitLemmas.bool_and_right r2
  have r1 := Anneal.InitLemmas.bool_and_left r2
  have h1 := Anneal.InitLemmas.bool_and_right r1
  have r0 := Anneal.InitLemmas.bool_and_left r1
  have hS := Anneal.InitLemmas.bool_and_right r0
  have h0 := Anneal.InitLemmas.bool_and_left r0
  exact ⟨Nat.le_of_ble_eq_true h0, Nat.le_of_ble_eq_true hS,
    Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2,
    Nat.le_of_ble_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.le_of_ble_eq_true h6⟩

/-- Witness-free relational gate for slice-DST cast metadata. -/
@[expose] def sliceDstCastGate :
    CertifiedGate DstCastInput (Nat × Nat) Unit (fun _ => True)
      ValidDstCast :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun x out _ => checkDstCast x out
    sound := fun x out _ _ _ h => checkDstCast_sound x out h }

/-- 26 bytes at a 4-aligned address, a 4-byte header, 6-byte elements,
alignment 4, prefix cast. Three elements need 24 bytes and four need 28. -/
@[expose] def castIn : DstCastInput :=
  { addr := 4096, bytesLen := 26, align := 4, sizeBase := 4, phase := 0,
    elemSize := 6, sizeAlign := 4, isPrefix := true }

/-- The same input as a suffix cast, which starts at `4098`. -/
@[expose] def castInSuffix : DstCastInput :=
  { castIn with isPrefix := false }

/-- The maximal candidate is accepted after a trap and a sub-maximal
candidate, and it is valid. -/
theorem canary_dst_portfolio :
    firstAccepted sliceDstCastGate castIn
        ([.trapped, .candidate (2, 16) (), .candidate (3, 24) ()] :
          List (RawOutcome Unit (Nat × Nat) Unit)) = .ok (3, 24) ∧
    ValidDstCast castIn (3, 24) :=
  ⟨rfl, evalGate_sound (E := Unit) sliceDstCastGate castIn
    (.candidate (3, 24) ()) (3, 24) True.intro rfl⟩

/-- Two elements fit, but so do three, so `(2, 16)` is not maximal. -/
theorem canary_dst_submaximal_invalid : ¬ ValidDstCast castIn (2, 16) :=
  fun h => absurd h.2.2.2.2.2.2.2 (by decide)

/-- The sub-maximal candidate and the misaligned suffix cast are rejected.
-/
theorem canary_dst_rejections :
    evalGate (E := Unit) sliceDstCastGate castIn (.candidate (2, 16) ()) =
      .error .rejectedByChecker ∧
    evalGate (E := Unit) sliceDstCastGate castInSuffix
        (.candidate (3, 2) ()) = .error .rejectedByChecker :=
  ⟨rfl, rfl⟩

/-- A `repr(packed(2))` wrapper: pointer alignment 2, size alignment 4. At
address 2, two 2-byte elements round up to 4 bytes and fit in 6; three
round up to 8 and do not. With a single alignment of 4 the address would be
rejected. -/
@[expose] def castInPacked : DstCastInput :=
  { addr := 2, bytesLen := 6, align := 2, sizeBase := 0, phase := 0,
    elemSize := 2, sizeAlign := 4, isPrefix := true }

theorem canary_dst_packed :
    evalGate (E := Unit) sliceDstCastGate castInPacked
        (.candidate (2, 4) ()) = .ok (2, 4) ∧
    evalGate (E := Unit) sliceDstCastGate castInPacked
        (.candidate (3, 6) ()) = .error .rejectedByChecker ∧
    evalGate (E := Unit) sliceDstCastGate
        { castInPacked with align := 4 } (.candidate (2, 4) ()) =
      .error .rejectedByChecker :=
  ⟨rfl, rfl, rfl⟩

/-- `ValidDstCast` distinguishes two accepted (`some`) outputs. -/
theorem canary_dst_accepted_dichotomy :
    Anneal.Core.DichotomyModuloObservation (fun _ o => Option.isSome o)
      (fun _ => True) (optionLift ValidDstCast) :=
  optionLift_acceptedDichotomy castIn True.intro (3, 24) (2, 16)
    canary_dst_portfolio.2 canary_dst_submaximal_invalid

/-! ## In-process producers -/

/-- Only freedom from undefined behavior; nothing about memory. -/
@[expose] def wfOnlyProducerContract {Mem X Ret : Type}
    (sPre bPre : Mem × X → Prop) (eff : EffectMask) :
    FnContract (Mem × X) Ret Mem :=
  { safetyPre := sPre, behaviorPre := bPre, effects := eff }

/-- All three effect guarantees. -/
@[expose] def totalMask : EffectMask :=
  { terminates := true, noUnwind := true, noAbort := true }

/-- Returns a wrong candidate after zeroing caller memory. -/
@[expose] def clobberProducer (q : Nat × Nat)
    (o : RunOutcome (Nat × Unit) Nat) : Prop :=
  o = .terminal (.returned (q.2 + 999, ()) 0)

/-- Returns the same wrong candidate with caller memory unchanged. -/
@[expose] def keepProducer (q : Nat × Nat)
    (o : RunOutcome (Nat × Unit) Nat) : Prop :=
  o = .terminal (.returned (q.2 + 999, ()) q.1)

/-- Output must be `x + mem`, with memory unchanged. -/
@[expose] def sumPost (q : Nat × Nat) (y : Nat) (m' : Nat) : Prop :=
  y = q.2 + q.1 ∧ m' = q.1

@[expose] def sumCheck (q : Nat × Nat) (y : Nat) (_ : Unit) : Bool :=
  Nat.beq y (q.2 + q.1)

@[expose] def keepMem (q : Nat × Nat) (_ : Nat) : Nat := q.1

@[expose] def sumFb (q : Nat × Nat) : Nat × Nat := (q.2 + q.1, q.1)

theorem sumCheck_sound (q : Nat × Nat) (y : Nat) (w : Unit)
    (h : sumCheck q y w = true) : sumPost q y (keepMem q y) :=
  ⟨Nat.eq_of_beq_eq_true h, rfl⟩

theorem sumFb_sound (q : Nat × Nat) : sumPost q (sumFb q).1 (sumFb q).2 :=
  ⟨rfl, rfl⟩

/-- A producer free of undefined behavior that zeroes caller memory makes
the checker and fallback read the wrong memory: on `(mem, x) = (10, 5)`
the composition returns `5` with memory `0`. -/
theorem rung15_without_callerMemPreserved_unsound :
    ContractHolds
        (wfOnlyProducerContract (fun _ => True) (fun q => q.1 = 10) totalMask)
        false clobberProducer ∧
    ¬ ContractHolds
        (rung15OuterContract (fun _ => True) (fun q => q.1 = 10) sumPost
          totalMask)
        false (rung15Run clobberProducer sumCheck keepMem sumFb) := by
  refine ⟨⟨fun _ _ h => (by cases h), fun _ _ o h => ?_⟩, fun hC => ?_⟩
  · have h' : o = .terminal (.returned (_ + 999, ()) 0) := h
    rw [h']
    exact True.intro
  · have hBad : (5 = 5 + 10 ∧ (0 : Nat) = 10) :=
      hC.2 (10, 5) ⟨fun _ => True.intro, rfl⟩ (.terminal (.returned 5 0))
        ⟨_, rfl, rfl⟩
    exact absurd hBad.2 (by decide)

/-- The same wrong candidate from a memory-preserving producer is
harmless. -/
theorem canary_rung15_preserving :
    ContractHolds
      (rung15OuterContract (fun _ => True) (fun q => q.1 = 10) sumPost
        totalMask)
      false (rung15Run keepProducer sumCheck keepMem sumFb) := by
  refine rung15_with_callerMemPreserved_sound _ _ sumPost totalMask totalMask
    false keepProducer sumCheck keepMem sumFb (maskLe_refl _)
    ⟨fun _ _ h => (by cases h), fun q _ o h => ?_⟩
    (fun q y w _ h => sumCheck_sound q y w h) (fun q _ => sumFb_sound q)
  have h' : o = .terminal (.returned (q.2 + 999, ()) q.1) := h
  rw [h']
  exact rfl

/-! ## Anti-vacuity -/

/-- A single-body model whose body returns `impl q`. -/
@[expose] def toyModel (impl : Nat → Option Nat) :
    ExecutionModel Unit Unit Unit Nat (Option Nat) Unit :=
  { profileId := "toy"
    oracleGrade := .unbridged "toy"
    programAdmitted := fun _ => true
    bodyAdmitted := fun _ _ => true
    isPartialScope := fun _ => false
    bodyAt := fun _ _ => some ()
    uniqueIdentities := fun _ => true
    bodyIdentity := fun _ => "toy"
    bodyIsUnsafe := fun _ => false
    bodyIsExternal := fun _ => false
    bodyMatchesSig := fun _ _ => true
    modelGaps := []
    requiredGaps := fun _ => []
    claimShapeGaps := fun _ => []
    entryDom := fun _ _ => True
    returnValid := fun _ _ _ => True
    memValid := fun _ => True
    execForBody := fun p _ => p
    wellFormed := fun _ _ => True
    produces := fun _ q o => o = .returned (impl q) ()
    diverges := fun _ _ => False
    faultsUB := fun _ _ => False }

@[expose] def toyContract : FnContract Nat (Option Nat) Unit :=
  { effects := totalMask }

/-- An accepting body has an accepted witness; an always-`none` body, which
meets every `optionLift` specification, has none. -/
theorem canary_hasAcceptedWitness :
    HasAcceptedWitness (toyModel some) () 0 () toyContract Option.isSome ∧
    ¬ HasAcceptedWitness (toyModel (fun _ => none)) () 0 () toyContract
      Option.isSome := by
  refine ⟨⟨rfl, 0, some 0, (), True.intro,
    ⟨fun h => (by cases h), True.intro⟩, rfl, rfl⟩, ?_⟩
  refine not_hasAcceptedWitness_of_alwaysRejects _ _ _ _ _ _ ?_
  intro q r m h
  have h' : TerminalOutcome.returned r m = .returned none () := h
  injection h' with hr
  rw [hr]
  rfl

/-- The witness is tied to the body stored at `defId`: a model with no body
there has no accepted witness, even though its execution accepts. -/
theorem canary_hasAcceptedWitness_requires_bodyAt :
    ¬ HasAcceptedWitness { toyModel some with bodyAt := fun _ _ => none } ()
      0 () toyContract Option.isSome :=
  fun h => by
    have hNone : (none : Option Unit) = some () := h.bodyAt_eq
    cases hNone

/-! ## Ratchets -/

/-- No effect guarantees. -/
@[expose] def anyExitMask : EffectMask :=
  { terminates := false, noUnwind := false, noAbort := false }

/-- One producer that proposes `x`. -/
@[expose] def singleProducer : HybridComponent Nat Unit Nat :=
  { mask := anyExitMask
    run := fun x => evalGate eqGate x (.candidate x ()) }

/-- A portfolio whose first producer is wrong and whose second proposes `x`,
with stronger effect guarantees. -/
@[expose] def portfolio : HybridComponent Nat Unit Nat :=
  { mask := totalMask
    run := fun x =>
      firstAccepted eqGate x [.candidate (x + 1) (), .candidate x ()] }

theorem portfolio_sound :
    ResultSound (fun _ => True) (fun x y => y = x) portfolio.run :=
  fun x _ y h =>
    firstAccepted_sound eqGate x [.candidate (x + 1) (), .candidate x ()] y
      True.intro h

theorem singleProducer_sound :
    ResultSound (fun _ => True) (fun x y => y = x) singleProducer.run :=
  fun x _ y h => evalGate_sound eqGate x (.candidate x ()) y True.intro h

theorem evalGate_eqGate_self (x : Nat) :
    evalGate (E := Unit) eqGate x (.candidate x ()) = .ok x :=
  (evalGate_candidate_ok_iff eqGate x x () x).2
    ⟨rfl, Nat.le_refl 0, Nat.beq_refl x⟩

/-- The portfolio may replace the single producer, and because the
specification determines the output, it returns the same output. -/
theorem canary_ratchet :
    HybridRefines (fun _ => True) (fun x y => y = x) singleProducer
        portfolio ∧
    ∀ x, portfolio.run x = .ok x := by
  have hRef : HybridRefines (fun _ => True) (fun x y => y = x)
      singleProducer portfolio :=
    ⟨⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
        fun h => Bool.noConfusion h⟩,
      portfolio_sound,
      fun x _ _ _ => (firstAccepted_ok_iff_exists eqGate x _).2
        ⟨.candidate x (), List.Mem.tail _ (List.Mem.head _), x,
          evalGate_eqGate_self x⟩⟩
  exact ⟨hRef, fun x =>
    hybridRefines_pointwise_of_deterministic
      (fun _ _ _ _ h1 h2 => h1.trans h2.symm) singleProducer_sound hRef x
      True.intro x (evalGate_eqGate_self x)⟩

/-- A caller that doubles the component's output. -/
@[expose] def doubleOuter (f : Nat → Except (HybridErr Unit) Nat) (x : Nat) :
    Except Unit Nat :=
  match f x with
  | .ok y => .ok (y + y)
  | .error _ => .error ()

/-- The caller's proof for every sound component carries over to the
portfolio. -/
theorem canary_ratchet_outer (x z : Nat)
    (h : doubleOuter portfolio.run x = .ok z) : z = x + x := by
  have hOuter : ∀ f, ResultSound (fun _ => True) (fun x y => y = x) f →
      ∀ x, True → ∀ z, doubleOuter f x = .ok z → z = x + x := by
    intro f hf x hx z h
    revert h
    dsimp only [doubleOuter]
    cases hfx : f x with
    | error _ => intro h; cases h
    | ok y =>
      intro h
      injection h with h
      rw [← h, hf x hx y hfx]
  exact (ratchet_result_preserves_outer_safety_and_availability doubleOuter
    (fun x z => z = x + x) hOuter canary_ratchet.1).1 x True.intro z h

/-! ## Integer cuts -/

/-- `(-2) * x - y ≤ 5 → -3 ≤ -y → -4 ≤ x` through the integer-cut gate. -/
theorem canary_intCut (x y : Int)
    (h1 : Int.sub (Int.mul (Int.negOfNat 2) x) y ≤ Int.ofNat 5)
    (h2 : Int.negOfNat 3 ≤ Int.neg y) : Int.negOfNat 4 ≤ x :=
  certGateCut_sound (intCutGate 8) (x := Anneal.LinearArith.intSubNegMulGoal)
    (y := ()) (w := Anneal.LinearArith.intSubNegMulCert) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl) [x, y] h1 h2

/-! ## Bridges -/

/-- `maskLe` is `Anneal.Framework.effectMaskLe`. -/
theorem maskLe_eq_effectMaskLe : maskLe = Anneal.Framework.effectMaskLe :=
  rfl

end Anneal.Hybrid.Canaries

end
