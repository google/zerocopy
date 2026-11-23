-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence

namespace Anneal.MirCorrespondence.MemoryLemmas

open Miri.ABI

/-!
# Zero-patch memory specification lemmas

Port of `google/zerocopy#4022`'s 47 Pass-1-admissible public specification
theorems (and corresponding non-vacuity witnesses) about
`Miri.Memory.{InitMask, ProvenanceMap, Allocation}` into Pass 2 untrusted
`correspondence/`, leaving `vendor/lean-miri/` unmodified for those 3 memory
modules (#4009). Three remaining `#4022` theorems
(`InitMask.WriteProof.prepareCopy_of_uniform`,
`Allocation.copyRepeatedly_initialized_spec`, and
`Allocation.copy_initialized_spec`, plus witnesses invoking them) depend on
unfolding `_private...Miri.Memory.InitMask.collectChunksAux`, which is marked
`private` and implicitly `@[irreducible]` under unmodified `InitMask.lean`, and
are deferred to a small follow-up PR so this change stays strictly Pass 1 clean
with zero edits to `TrustedBoundary.lean` or `vendor/lean-miri/Miri/Memory/*`.

Because `Miri.Memory.{InitMask, ProvenanceMap, Allocation}` mark internal
helpers (`checkedSlice`, `setInitialization`, `overwriteRawBytes`,
`setRangeInbounds`, `findBit`, `materialize`, `targetUIntBytes`,
`readTargetUInt`, `Allocation.mk`, and `rawBytes`) as `private`, this module
mirrors them under `Mirrors` and certifies every public operation mirror with an
`@op = @opR := rfl` bridge in the Lean kernel.
-/

/-! ## Shared Pass-1 Helpers -/

private theorem if_pos_eq {α : Type} {c : Prop} [hdec : Decidable c]
    {t e : α} (h : c) : (if c then t else e) = t := by
  cases hdec with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem if_neg_eq {α : Type} {c : Prop} [hdec : Decidable c]
    {t e : α} (h : ¬c) : (if c then t else e) = e := by
  cases hdec with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

private theorem div_mul_64_add_mod (n : Nat) :
    (HDiv.hDiv n 64) * 64 + HMod.hMod n 64 = n := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod n 64

private theorem nat_lt_div_of_lt_mul_64 {a b : Nat} (h : a < b * 64) :
    HDiv.hDiv a 64 < b :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)

private theorem div_mod_64_of_eq {n blk bit : Nat} (h_bit : bit < 64)
    (h_eq : n = blk * 64 + bit) :
    HDiv.hDiv n 64 = blk ∧ HMod.hMod n 64 = bit := by
  subst h_eq
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt h_bit, Nat.zero_add]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h_bit]

private theorem mul64_add_lt_of_lt_blk {a b c d : Nat} (hb : b < 64) (hab : a < c) :
    a * 64 + b < c * 64 + d := by
  have h1 : a * 64 + b < (a + 1) * 64 := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left hb (a * 64)
  have h2 : (a + 1) * 64 ≤ c * 64 := Nat.mul_le_mul_right 64 hab
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (Nat.le_add_right (c * 64) d))

private theorem mul64_add_le_of_lt_blk {a b c d : Nat} (hb : b < 64) (hab : a < c) :
    a * 64 + b ≤ c * 64 + d :=
  Nat.le_of_lt (mul64_add_lt_of_lt_blk hb hab)

private theorem add_lt_of_lt_sub_left {a b c : Nat} (h : b < c - a) : a + b < c := by
  rw [Nat.add_comm]
  exact Nat.add_lt_of_lt_sub h

private theorem nat_sub_add_sub_cancel {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    (b - a) + (c - b) = c - a := by
  apply Nat.add_right_cancel (m := a)
  rw [Nat.add_assoc, Nat.add_comm (c - b) a, ← Nat.add_assoc, Nat.sub_add_cancel h1,
    Nat.add_comm b (c - b), Nat.sub_add_cancel h2, Nat.sub_add_cancel (Nat.le_trans h1 h2)]

private theorem nat_sub_sub_sub_cancel_right {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    (c - a) - (b - a) = c - b :=
  (Nat.sub_eq_iff_eq_add (Nat.sub_le_sub_right h2 a)).mpr
    (by rw [Nat.add_comm]; exact (nat_sub_add_sub_cancel h1 h2).symm)

private theorem lt_blk_of_mul64_add_lt {a b c d : Nat} (hd : d < 64)
    (h_ne : a ≠ c) (h_lt : a * 64 + b < c * 64 + d) : a < c := by
  cases Nat.lt_or_gt_of_ne h_ne with
  | inl h => exact h
  | inr h => exact absurd (mul64_add_lt_of_lt_blk hd h) (Nat.not_lt.mpr (Nat.le_of_lt h_lt))

private theorem le_blk_of_mul64_add_le {a b c d : Nat} (hd : d < 64)
    (h_le : a * 64 + b ≤ c * 64 + d) : a ≤ c := by
  cases Nat.lt_or_ge c a with
  | inl h => exact absurd (mul64_add_lt_of_lt_blk hd h) (Nat.not_lt.mpr h_le)
  | inr h => exact h

private theorem two_pow_64_lt_128 : HPow.hPow (2 : Nat) 64 < HPow.hPow (2 : Nat) 128 := by
  decide

private theorem add_lt_two_pow_64_of_not_wrap {a b : Nat}
    (ha : a < HPow.hPow (2 : Nat) 64) (hb : b < HPow.hPow (2 : Nat) 64)
    (h_nw : ¬(HMod.hMod (a + b) (HPow.hPow (2 : Nat) 64) < a)) :
    a + b < HPow.hPow (2 : Nat) 64 := by
  cases Nat.lt_or_ge (a + b) (HPow.hPow (2 : Nat) 64) with
  | inl h => exact h
  | inr h =>
    have h_sub_lt : a + b - HPow.hPow (2 : Nat) 64 < HPow.hPow (2 : Nat) 64 := by
      have h1 : a + b < a + HPow.hPow (2 : Nat) 64 := Nat.add_lt_add_left hb a
      have h2 : a + HPow.hPow (2 : Nat) 64 < HPow.hPow (2 : Nat) 64 + HPow.hPow (2 : Nat) 64 :=
        Nat.add_lt_add_right ha _
      exact Nat.sub_lt_left_of_lt_add h (Nat.lt_trans h1 h2)
    have h_mod : HMod.hMod (a + b) (HPow.hPow (2 : Nat) 64) = a + b - HPow.hPow (2 : Nat) 64 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt h_sub_lt]
    have h_wrap : HMod.hMod (a + b) (HPow.hPow (2 : Nat) 64) < a := by
      rw [h_mod]
      exact Nat.sub_lt_left_of_lt_add h (by rw [Nat.add_comm (HPow.hPow 2 64) a]; exact Nat.add_lt_add_left hb a)
    exact absurd h_wrap h_nw


/-! ## Part 1. `InitMask` -/

/-! ### 1a. Private mirrors of private `Miri.Memory` `InitMask` helpers -/

namespace Mirrors
open Miri.ABI
open Miri.Memory

private def maxSizeBytes : Nat := 18446744073709551615

private theorem le_maxSizeBytes_of_lt {n : Nat} (h : n < HPow.hPow (2 : Nat) 64) :
    n ≤ maxSizeBytes := Nat.le_trans (Nat.le_pred_of_lt h) (by decide)
private def wordMask : Nat := 18446744073709551615
private def blockSize : Nat := 64
private def sizeBytes (size : Size) : Nat := size.bytes.toNat

private def sizeFromNat (n : Nat) : Except InitMaskError Size :=
  if n ≤ maxSizeBytes then .ok (Size.ofBytes (UInt64.ofNat n))
  else .error (.sizeFromNatOverflow n)

private def bitAt (word bit : Nat) : Bool := Nat.testBit word bit

private def setWordRange (word lo hi : Nat) (state : Bool) : UInt64 :=
  let mask := (HPow.hPow (2 : Nat) hi - 1) - (HPow.hPow (2 : Nat) lo - 1)
  UInt64.ofNat (if state then Nat.lor word mask else Nat.land word (wordMask - mask))

namespace InitMaskMaterialized

private def bitIndexR (offset : Size) : Nat × Nat :=
  let bytes := sizeBytes offset
  (HDiv.hDiv bytes blockSize, HMod.hMod bytes blockSize)

private def sizeFromBitIndex (block bit : Nat) : Except InitMaskError Size :=
  sizeFromNat (block * blockSize + bit)

private def getBlock (self : Miri.Memory.InitMaskMaterialized) (block : Nat) :
    Except InitMaskError UInt64 :=
  match self.blocks[block]? with
  | some word => .ok word
  | none => .error (.blockIndexOutOfBounds block self.blocks.size)

private def setBlock (blocks : Array UInt64) (index : Nat) (word : UInt64) :
    Except InitMaskError (Array UInt64) :=
  if h : index < blocks.size then
    .ok (blocks.set index word h)
  else
    .error (.blockIndexOutOfBounds index blocks.size)

private def get (self : Miri.Memory.InitMaskMaterialized) (offset : Size) :
    Except InitMaskError Bool :=
  let (block, bit) := bitIndexR offset
  Bind.bind (getBlock self block) fun word =>
    Pure.pure (bitAt word.toNat bit)

private def setRangeInbounds (self : Miri.Memory.InitMaskMaterialized)
    (start finish : Size) (newState : Bool) :
    Except InitMaskError Miri.Memory.InitMaskMaterialized :=
  let (blockA, bitA) := bitIndexR start
  let (blockB, bitB) := bitIndexR finish
  have words := self.blocks
  have kEnd := fun (_r : Unit) words => Pure.pure (Miri.Memory.InitMaskMaterialized.mk words)
  if blockA == blockB then
    have endBit := if bitB == 0 then 64 else bitB
    Bind.bind (getBlock ⟨words⟩ blockA) fun word =>
      Bind.bind (setBlock words blockA (setWordRange word.toNat bitA endBit newState)) fun words =>
        kEnd Unit.unit words
  else if newState then
    Bind.bind (getBlock ⟨words⟩ blockA) fun wordA =>
      Bind.bind (setBlock words blockA (setWordRange wordA.toNat bitA 64 true)) fun words =>
        have kLoop := fun (_r : Unit) words =>
          Bind.bind
            (forIn ({ start := blockA + 1, stop := blockB,
                      step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
              words
              fun block s =>
                have words := s
                Bind.bind (setBlock words block (UInt64.ofNat wordMask)) fun words =>
                  Pure.pure (ForInStep.yield words))
            fun s =>
              have words := s
              kEnd Unit.unit words
        if bitB != 0 then
          Bind.bind (getBlock ⟨words⟩ blockB) fun wordB =>
            Bind.bind (setBlock words blockB (setWordRange wordB.toNat 0 bitB true)) fun words =>
              kLoop Unit.unit words
        else kLoop Unit.unit words
  else
    Bind.bind (getBlock ⟨words⟩ blockA) fun wordA =>
      Bind.bind (setBlock words blockA (setWordRange wordA.toNat bitA 64 false)) fun words =>
        have kLoop := fun (_r : Unit) words =>
          Bind.bind
            (forIn ({ start := blockA + 1, stop := blockB,
                      step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
              words
              fun block s =>
                have words := s
                Bind.bind (setBlock words block 0) fun words =>
                  Pure.pure (ForInStep.yield words))
            fun s =>
              have words := s
              kEnd Unit.unit words
        if bitB != 0 then
          Bind.bind (getBlock ⟨words⟩ blockB) fun wordB =>
            Bind.bind (setBlock words blockB (setWordRange wordB.toNat 0 bitB false)) fun words =>
              kLoop Unit.unit words
        else kLoop Unit.unit words

private def grow (self : Miri.Memory.InitMaskMaterialized) (len amount : Size)
    (newState : Bool) : Except InitMaskError Miri.Memory.InitMaskMaterialized :=
  have amountBytes := sizeBytes amount
  if amountBytes == 0 then Pure.pure self
  else
    have lenBytes := sizeBytes len
    have capacity := self.blocks.size * blockSize
    have kAfterCap := fun (_r : Unit) =>
      have unusedTrailingBits := capacity - lenBytes
      have words := self.blocks
      have kGrow := fun (_r : Unit) words =>
        have kRet := fun (_r : Unit) words => Pure.pure (Miri.Memory.InitMaskMaterialized.mk words)
        if unusedTrailingBits > 0 then
          Bind.bind (sizeFromNat (lenBytes + unusedTrailingBits)) fun tailEnd =>
            Bind.bind (setRangeInbounds ⟨words⟩ len tailEnd newState) fun grown =>
              have words := grown.blocks
              kRet Unit.unit words
        else kRet Unit.unit words
      if amountBytes > unusedTrailingBits then
        have additionalBlocks := HDiv.hDiv amountBytes blockSize + 1
        have word := if newState then UInt64.ofNat wordMask else 0
        have words := words ++ Array.replicate additionalBlocks word
        kGrow Unit.unit words
      else kGrow Unit.unit words
    if capacity < lenBytes then
      Bind.bind (throw (.blockCapacityTooSmall lenBytes capacity)) fun r => kAfterCap r
    else kAfterCap Unit.unit

private def firstSetBit (word startBit : Nat) : Option Nat :=
  ((List.range (64 - startBit)).find? fun offset =>
    bitAt word (startBit + offset)).map (· + startBit)

private def searchBlock (word : UInt64) (block startBit : Nat)
    (isInit : Bool) : Except InitMaskError (Option Size) :=
  have bits := if isInit then word.toNat else wordMask - word.toNat
  match firstSetBit bits startBit with
  | none => Pure.pure none
  | some bit => Bind.bind (sizeFromBitIndex block bit) fun sz => Pure.pure (some sz)

private def findBitFast (self : Miri.Memory.InitMaskMaterialized)
    (start finish : Size) (isInit : Bool) : Except InitMaskError (Option Size) :=
  have startBytes := sizeBytes start
  have finishBytes := sizeBytes finish
  if startBytes >= finishBytes then Pure.pure none
  else
    let (startBlock, startBit) := bitIndexR start
    Bind.bind (sizeFromNat (finishBytes - 1)) fun endInclusive =>
      let (endBlockInclusive, _) := bitIndexR endInclusive
      Bind.bind (getBlock self startBlock) fun w0 =>
        Bind.bind (searchBlock w0 startBlock startBit isInit) fun first =>
          match first with
          | some index =>
            if sizeBytes index < finishBytes then Pure.pure (some index) else Pure.pure none
          | none =>
            have kNone := fun (_r : Unit) => Pure.pure none
            if startBlock < endBlockInclusive then
              Bind.bind
                (forIn
                  ({ start := startBlock + 1, stop := endBlockInclusive + 1,
                     step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
                  ((none : Option (Option Size)), Unit.unit)
                  fun block _ =>
                    Bind.bind (getBlock self block) fun w =>
                      Bind.bind (searchBlock w block 0 isInit) fun
                        | some index =>
                          if sizeBytes index < finishBytes then
                            Pure.pure (ForInStep.done (some (some index), Unit.unit))
                          else Pure.pure (ForInStep.done (some none, Unit.unit))
                        | none => Pure.pure (ForInStep.yield (none, Unit.unit)))
                fun s =>
                  have r := s
                  Break.runK.match_1 (fun _ => Except InitMaskError (Option Size)) r.1
                    (fun r => Pure.pure r) fun _ => kNone Unit.unit
            else kNone Unit.unit

private def findBit (self : Miri.Memory.InitMaskMaterialized)
    (start finish : Size) (isInit : Bool) : Except InitMaskError (Option Size) :=
  findBitFast self start finish isInit

end InitMaskMaterialized

namespace InitMask

private def materialize (self : Miri.Memory.InitMask) :
    Except InitMaskError Miri.Memory.InitMaskMaterialized :=
  match self.blocks with
  | .Lazy state => InitMaskMaterialized.grow ⟨List.nil.toArray⟩ (Size.ofBytes 0) self.len state
  | .Materialized blocks => Pure.pure blocks

/-! ### 1b. Mirrors of public `InitMask` operations and `rfl` bridges -/

private def getR (self : Miri.Memory.InitMask) (index : Size) :
    Except InitMaskError Bool :=
  match self.blocks with
  | .Lazy state => Pure.pure state
  | .Materialized blocks => InitMaskMaterialized.get blocks index

private def isRangeInitializedR (self : Miri.Memory.InitMask) (range : AllocRange) :
    Except InitMaskError (Except AllocRange Unit) :=
  Bind.bind range.endExclusive fun finish =>
    if finish.bytes > self.len.bytes then
      Bind.bind (AllocRange.fromEndpoints self.len finish) fun r => Pure.pure (.error r)
    else
      match self.blocks with
      | .Lazy state =>
        if state then Pure.pure (.ok Unit.unit) else Pure.pure (.error range)
      | .Materialized blocks =>
        Bind.bind (InitMaskMaterialized.findBit blocks range.start finish false) fun
          | none => Pure.pure (.ok Unit.unit)
          | some uninitStart =>
            Bind.bind (InitMaskMaterialized.findBit blocks uninitStart finish true) fun f =>
              have uninitEnd := f.getD finish
              Bind.bind (AllocRange.fromEndpoints uninitStart uninitEnd) fun r =>
                Pure.pure (.error r)

private def setRangeR (self : Miri.Memory.InitMask) (range : AllocRange)
    (newState : Bool) : Except InitMaskError Miri.Memory.InitMask :=
  have start := range.start
  Bind.bind range.endExclusive fun finish =>
    let fullOverwrite := start.bytes = 0 ∧ self.len.bytes ≤ finish.bytes
    match self.blocks with
    | .Lazy state =>
      if fullOverwrite then Pure.pure ⟨.Lazy newState, finish⟩
      else if state == newState then
        if finish.bytes > self.len.bytes then Pure.pure ⟨.Lazy state, finish⟩
        else Pure.pure self
      else
        Bind.bind (materialize self) fun blocks =>
          if finish.bytes ≤ self.len.bytes then
            Bind.bind (InitMaskMaterialized.setRangeInbounds blocks start finish newState) fun b =>
              Pure.pure ⟨.Materialized b, self.len⟩
          else
            have kFinish := fun firstPart =>
              Bind.bind ((Size.sub finish self.len).mapError MemoryError.sizeError) fun amount =>
                Bind.bind (InitMaskMaterialized.grow firstPart self.len amount newState) fun b =>
                  Pure.pure ⟨.Materialized b, finish⟩
            if start.bytes < self.len.bytes then
              Bind.bind (InitMaskMaterialized.setRangeInbounds blocks start self.len newState)
                fun firstPart => kFinish firstPart
            else
              Bind.bind (Pure.pure blocks) fun firstPart => kFinish firstPart
    | .Materialized oldBlocks =>
      if fullOverwrite then Pure.pure ⟨.Lazy newState, finish⟩
      else if finish.bytes ≤ self.len.bytes then
        Bind.bind (InitMaskMaterialized.setRangeInbounds oldBlocks start finish newState) fun b =>
          Pure.pure ⟨.Materialized b, self.len⟩
      else
        have kFinish := fun firstPart =>
          Bind.bind ((Size.sub finish self.len).mapError MemoryError.sizeError) fun amount =>
            Bind.bind (InitMaskMaterialized.grow firstPart self.len amount newState) fun b =>
              Pure.pure ⟨.Materialized b, finish⟩
        if start.bytes < self.len.bytes then
          Bind.bind (InitMaskMaterialized.setRangeInbounds oldBlocks start self.len newState)
            fun firstPart => kFinish firstPart
        else
          Bind.bind (Pure.pure oldBlocks) fun firstPart => kFinish firstPart


private theorem get_eq_getR : @Miri.Memory.InitMask.get = @getR := rfl
private theorem isRangeInitialized_eq_R :
    @Miri.Memory.InitMask.isRangeInitialized = @isRangeInitializedR := rfl
private theorem setRange_eq_R : @Miri.Memory.InitMask.setRange = @setRangeR := rfl

end InitMask


end Mirrors

/-! ### 1c. `WriteProof` helpers over the mirrors -/

namespace InitMask.WriteProof
open Miri.ABI Miri.Memory
variable {ε α β : Type}

private abbrev getBlock := @Mirrors.InitMaskMaterialized.getBlock
private abbrev setBlock := @Mirrors.InitMaskMaterialized.setBlock
private abbrev setRangeInbounds := @Mirrors.InitMaskMaterialized.setRangeInbounds
private abbrev materialize := @Mirrors.InitMask.materialize
private abbrev setWordRange := @Mirrors.setWordRange
private abbrev wordMask := @Mirrors.wordMask

private theorem get_block_ok (words : Array UInt64) (index : Nat) (inBounds : index < words.size) :
    getBlock ⟨words⟩ index = .ok (GetElem.getElem words index inBounds) := by
  unfold getBlock
  unfold Mirrors.InitMaskMaterialized.getBlock
  simp [Array.getElem?_eq_getElem inBounds]

private def write_step (word : UInt64) (index : Nat) (words : Array UInt64) :
    Except InitMaskError (ForInStep (Array UInt64)) :=
  Bind.bind (setBlock words index word) fun updated =>
    Pure.pure (.yield updated)

private def update_word (words : Array UInt64) (index : Nat) (transform : UInt64 → UInt64) :
    Except InitMaskError (Array UInt64) :=
  Bind.bind (getBlock ⟨words⟩ index) fun word =>
    setBlock words index (transform word)

private def set_range_words (words : Array UInt64) (blockA bitA blockB bitB : Nat) (state : Bool) :
    Except InitMaskError (Array UInt64) :=
  if blockA == blockB then
    update_word words blockA (fun word => setWordRange word.toNat bitA (if bitB == 0 then 64 else bitB) state)
  else
    Bind.bind (update_word words blockA (fun word => setWordRange word.toNat bitA 64 state)) fun initial =>
      Bind.bind (if bitB != 0 then update_word initial blockB (fun word => setWordRange word.toNat 0 bitB state) else Pure.pure initial) fun middle =>
        forIn (Std.Legacy.Range.mk (blockA + 1) blockB 1 (by decide)) middle
          (write_step (if state then UInt64.ofNat wordMask else 0))

private theorem bind_if (p : Prop) [hdec : Decidable p] (yes no : Except ε α) (next : α → Except ε β) :
    Bind.bind (if p then yes else no) next = (if p then Bind.bind yes next else Bind.bind no next) := by
  cases hdec <;> rfl

private theorem set_range_inbounds_reduces (self : InitMaskMaterialized) (start finish : Size) (state : Bool) :
    setRangeInbounds self start finish state =
      Bind.bind (set_range_words self.blocks ((HDiv.hDiv start.bytes.toNat 64)) ((HMod.hMod start.bytes.toNat 64))
        ((HDiv.hDiv finish.bytes.toNat 64)) ((HMod.hMod finish.bytes.toNat 64)) state)
        fun words => Pure.pure ⟨words⟩ := by
  unfold setRangeInbounds
  unfold Mirrors.InitMaskMaterialized.setRangeInbounds
  unfold set_range_words update_word write_step getBlock setBlock setWordRange wordMask
  unfold Mirrors.InitMaskMaterialized.bitIndexR
  unfold Mirrors.sizeBytes
  unfold Mirrors.blockSize
  cases state <;> simp only [Bool.false_eq_true, reduceIte, bind_if, bind_assoc, pure_bind]

private theorem materialize_lazy_nonzero (len : Size) (state : Bool) (nonzero : len.bytes.toNat ≠ 0) :
    materialize (Miri.Memory.InitMask.new len state) = .ok ⟨Array.replicate ((HDiv.hDiv len.bytes.toNat 64) + 1) (if state then UInt64.ofNat 18446744073709551615 else 0)⟩ := by
  unfold materialize
  unfold Mirrors.InitMask.materialize
  unfold Miri.Memory.InitMask.new
  dsimp only
  unfold Mirrors.InitMaskMaterialized.grow
  unfold Mirrors.sizeBytes
  unfold Mirrors.blockSize
  unfold Mirrors.wordMask
  simp [nonzero, Size.ofBytes, Array.empty_append, Pure.pure, Except.pure]


/-! ### 1d. The six Pass-1 `InitMask.WriteProof` specification theorems -/



private theorem testBit_wordMask (bit : Nat) (h : bit < 64) :
    Nat.testBit wordMask bit = true := by
  have hm : wordMask = (HPow.hPow (2 : Nat) 64) - 1 := by decide
  rw [hm, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true h

private theorem setWordRange_testBit (word lo hi bit : Nat) (state : Bool)
    (h_lo_hi : lo ≤ hi) (h_hi : hi ≤ 64) (h_bit : bit < 64) :
    Nat.testBit (setWordRange word lo hi state).toNat bit =
      if lo ≤ bit ∧ bit < hi then state else Nat.testBit word bit := by
  let mask := ((HPow.hPow (2 : Nat) hi) - 1) - ((HPow.hPow (2 : Nat) lo) - 1)
  have h_pow_lo : 1 ≤ (HPow.hPow (2 : Nat) lo) := Nat.one_le_two_pow
  have h_pow_diff : 1 ≤ (HPow.hPow (2 : Nat) (hi - lo)) := Nat.one_le_two_pow
  have h_sum : mask = HShiftLeft.hShiftLeft ((HPow.hPow (2 : Nat) (hi - lo)) - 1) lo := by
    have h_eq : hi = lo + (hi - lo) := (Nat.add_sub_of_le h_lo_hi).symm
    have h_pow : (HPow.hPow (2 : Nat) hi) = (HPow.hPow (2 : Nat) lo) * (HPow.hPow (2 : Nat) (hi - lo)) :=
      (congrArg (HPow.hPow (2 : Nat)) h_eq).trans (Nat.pow_add 2 lo (hi - lo))
    have h_mul : (HPow.hPow (2 : Nat) lo) * ((HPow.hPow (2 : Nat) (hi - lo)) - 1) =
        (HPow.hPow (2 : Nat) lo) * (HPow.hPow (2 : Nat) (hi - lo)) - (HPow.hPow (2 : Nat) lo) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [Nat.shiftLeft_eq, Nat.mul_comm, h_mul, ← h_pow]
    dsimp only [mask]
    have h_pow_le : HPow.hPow (2 : Nat) lo ≤ HPow.hPow (2 : Nat) hi :=
      Nat.pow_le_pow_right (by decide) h_lo_hi
    rw [Nat.sub_sub, Nat.add_sub_of_le h_pow_lo]
  have h_mask_lt : mask < (HPow.hPow (2 : Nat) 64) := by
    have h_le64 : (HPow.hPow (2 : Nat) hi) ≤ (HPow.hPow (2 : Nat) 64) :=
      Nat.pow_le_pow_right (by decide) h_hi
    dsimp only [mask]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos hi) Nat.zero_lt_one) h_le64)
  have h_mask_bit : Nat.testBit mask bit = decide (lo ≤ bit ∧ bit < hi) := by
    rw [h_sum, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    cases Classical.em (lo ≤ bit) with
    | inl h_ge =>
      cases Classical.em (bit < hi) with
      | inl h_lt =>
        have : bit - lo < hi - lo := Nat.sub_lt_sub_right h_ge h_lt
        simp [h_ge, h_lt, this]
      | inr h_lt =>
        have : ¬(bit - lo < hi - lo) := fun h => h_lt (by
          have h1 := Nat.add_lt_add_left h lo
          rw [Nat.add_sub_of_le h_ge, Nat.add_sub_of_le h_lo_hi] at h1; exact h1)
        simp [h_ge, h_lt, this]
    | inr h_ge =>
      simp [h_ge]
  have h_inv : Nat.testBit (Mirrors.wordMask - mask) bit = !Nat.testBit mask bit := by
    have h_wm : Mirrors.wordMask = (HPow.hPow (2 : Nat) 64) - 1 := rfl
    rw [h_wm]
    have h_bv : BitVec.ofNat 64 ((HPow.hPow (2 : Nat) 64) - 1 - mask) = Complement.complement (BitVec.ofNat 64 mask) := by
      apply BitVec.eq_of_toNat_eq
      have h_sub_lt : HPow.hPow (2 : Nat) 64 - 1 - mask < HPow.hPow (2 : Nat) 64 :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos 64) Nat.zero_lt_one)
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_sub_lt, BitVec.toNat_not,
        Nat.mod_eq_of_lt h_mask_lt]
    have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
    simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
    exact h1
  unfold setWordRange Mirrors.setWordRange
  dsimp only
  cases state
  · simp only [Bool.false_eq_true, reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (HAnd.hAnd word (Mirrors.wordMask - mask)).testBit bit = _
    rw [Nat.testBit_and, h_inv, h_mask_bit]
    cases Classical.em (lo ≤ bit ∧ bit < hi) with
    | inl h_in => simp [h_in]
    | inr h_in => simp [h_in]
  · simp only [reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (HOr.hOr word mask).testBit bit = _
    rw [Nat.testBit_or, h_mask_bit]
    cases Classical.em (lo ≤ bit ∧ bit < hi) with
    | inl h_in => simp [h_in]
    | inr h_in => simp [h_in]

private theorem write_list_getElem? (indices : List Nat) (words : Array UInt64) (word : UInt64)
    (updated : Array UInt64)
    (h_ok : forIn indices words (write_step word) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if k ∈ indices then some word else words[k]? := by
  induction indices generalizing words with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, Except.pure, Except.ok.injEq] at h_ok
    subst h_ok
    exact ⟨rfl, fun _ => by simp⟩
  | cons first rest ih =>
    simp only [List.forIn_cons, write_step, Mirrors.InitMaskMaterialized.setBlock,
      setBlock, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases Classical.em (first < words.size) with
    | inl h_first =>
      simp only [h_first, reduceDIte] at h_ok
      let ⟨h_sz, h_elem⟩ := ih (words.set first word h_first) h_ok
      have h_wsz : (words.set first word h_first).size = words.size := Array.size_set _
      refine ⟨h_sz.trans h_wsz, fun k => ?_⟩
      rw [h_elem k]
      cases Classical.em (k ∈ rest) with
      | inl h_rest =>
        simp [h_rest]
      | inr h_rest =>
        simp only [h_rest, reduceIte, List.mem_cons, or_false]
        cases Classical.em (k = first) with
        | inl h_eq =>
          subst h_eq; simp [h_first]
        | inr h_eq =>
          simp [Ne.symm h_eq, h_eq]
    | inr h_first =>
      simp [h_first] at h_ok

private theorem write_range_getElem? (lower upper : Nat) (words : Array UInt64) (word : UInt64)
    (updated : Array UInt64)
    (h_ok : forIn (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one) words (write_step word) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if lower ≤ k ∧ k < upper then some word else words[k]? := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_ok
  let ⟨h_sz, h_elem⟩ := write_list_getElem? _ words word updated h_ok
  refine ⟨h_sz, fun k => ?_⟩
  rw [h_elem k]
  have h_mem : (k ∈ List.range' (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).start
      (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).size
      (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).step) ↔
      (lower ≤ k ∧ k < upper) := by
    simp only [List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul]
    constructor
    · intro ⟨i, hi, _heq⟩; subst _heq
      exact ⟨Nat.le_add_right lower i, add_lt_of_lt_sub_left hi⟩
    · intro ⟨h1, h2⟩
      exact ⟨k - lower, Nat.sub_lt_sub_right h1 h2, (Nat.add_sub_of_le h1).symm⟩
  cases Classical.em (lower ≤ k ∧ k < upper) with
  | inl h_in =>
    have hm : k ∈ List.range' (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).start
        (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).size
        (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).step := h_mem.mpr h_in
    rw [if_pos_eq (hm), if_pos_eq (h_in)]
  | inr h_in =>
    have hm : ¬(k ∈ List.range' (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).start
        (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).size
        (Std.Legacy.Range.mk lower upper 1 Nat.zero_lt_one).step) := fun h => h_in (h_mem.mp h)
    rw [if_neg_eq (hm), if_neg_eq (h_in)]

private theorem update_word_getElem? (words : Array UInt64) (index : Nat)
    (transform : UInt64 → UInt64) (updated : Array UInt64)
    (h_ok : update_word words index transform = .ok updated) :
    index < words.size ∧ updated.size = words.size ∧
      ∀ k, updated[k]? = if k = index then words[index]?.map transform else words[k]? := by
  unfold update_word getBlock Mirrors.InitMaskMaterialized.getBlock
    setBlock Mirrors.InitMaskMaterialized.setBlock at h_ok
  dsimp only at h_ok
  cases Classical.em (index < words.size) with
  | inl h_idx =>
    have h_get : words[index]? = some (GetElem.getElem words index h_idx) := Array.getElem?_eq_getElem h_idx
    simp only [h_get, Bind.bind, Except.bind, h_idx, reduceDIte, Except.ok.injEq] at h_ok
    subst h_ok
    refine ⟨h_idx, Array.size_set _, fun k => ?_⟩
    cases Classical.em (k = index) with
    | inl h_eq =>
      subst h_eq; simp [h_idx]
    | inr h_eq =>
      simp [Ne.symm h_eq, h_eq]
  | inr h_idx =>
    have h_get : words[index]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h_idx)
    simp [h_get, Bind.bind, Except.bind] at h_ok

private theorem set_range_words_bit_gen (words : Array UInt64) (bA rA bB rB : Nat) (state : Bool)
    (updated : Array UInt64)
    (h_rA : rA < 64) (h_rB : rB < 64)
    (h_nonempty : bA * 64 + rA < bB * 64 + rB)
    (h_ok : set_range_words words bA rA bB rB state = .ok updated) :
    updated.size = words.size ∧
      ∀ (k bit : Nat), k < words.size → bit < 64 →
        ∃ w oldW,
          updated[k]? = some w ∧
          words[k]? = some oldW ∧
          Nat.testBit w.toNat bit =
            if bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB then
              state
            else
              Nat.testBit oldW.toNat bit := by
  unfold set_range_words at h_ok
  cases Classical.em (bA == bB) with
  | inl h_same =>
    simp only [h_same, reduceIte] at h_ok
    have h_bA_eq : bA = bB := eq_of_beq h_same
    have h_rA_lt_rB : rA < rB := by
      rw [← h_bA_eq] at h_nonempty
      exact Nat.lt_of_add_lt_add_left h_nonempty
    have h_rB_nz : rB ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le rA) h_rA_lt_rB)
    let ⟨_, h_sz, h_elem⟩ := update_word_getElem? words bA _ updated h_ok
    refine ⟨h_sz, fun k bit h_ib h_bit => ?_⟩
    have h_old : words[k]? = some (GetElem.getElem words k h_ib) := Array.getElem?_eq_getElem h_ib
    cases Classical.em (k = bA) with
    | inl h_k =>
      subst h_k
      refine ⟨setWordRange (GetElem.getElem words k h_ib).toNat rA (if rB == 0 then 64 else rB) state,
        GetElem.getElem words k h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [if_pos_eq rfl, h_old] at he
        exact he
      · have h_rB_beq : (rB == 0) = false := beq_false_of_ne h_rB_nz
        simp only [h_rB_beq, Bool.false_eq_true, reduceIte]
        have h_lo_hi : rA ≤ rB := Nat.le_of_lt h_rA_lt_rB
        have h_hi : rB ≤ 64 := Nat.le_of_lt h_rB
        rw [setWordRange_testBit _ rA rB bit state h_lo_hi h_hi h_bit]
        have h_iff : (rA ≤ bit ∧ bit < rB) ↔ (k * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by
          rw [← h_bA_eq]
          exact ⟨fun ⟨h1, h2⟩ => ⟨Nat.add_le_add_left h1 _, Nat.add_lt_add_left h2 _⟩,
            fun ⟨h1, h2⟩ => ⟨Nat.le_of_add_le_add_left h1, Nat.lt_of_add_lt_add_left h2⟩⟩
        cases Classical.em (rA ≤ bit ∧ bit < rB) with
        | inl h1 =>
          rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
        | inr h1 =>
          rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
    | inr h_k =>
      refine ⟨GetElem.getElem words k h_ib, GetElem.getElem words k h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [if_neg_eq h_k] at he
        exact he.trans h_old
      · have h_out : ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by
          intro ⟨h1, h2⟩
          cases Nat.lt_or_gt_of_ne h_k with
          | inl hlt => exact Nat.not_lt_of_le h1 (mul64_add_lt_of_lt_blk h_bit hlt)
          | inr hgt =>
            rw [← h_bA_eq] at h2
            exact Nat.not_lt_of_le (Nat.le_of_lt (mul64_add_lt_of_lt_blk h_rB hgt)) h2
        rw [if_neg_eq h_out]
  | inr h_same =>
    simp only [h_same, Bool.false_eq_true, reduceIte] at h_ok
    have h_lt_div : bA < bB := by
      have h_ne : bA ≠ bB := fun h => h_same (beq_iff_eq.mpr h)
      exact lt_blk_of_mul64_add_lt h_rB h_ne h_nonempty
    cases h_init : update_word words bA (fun word => setWordRange word.toNat rA 64 state) with
    | error e => simp [h_init, Bind.bind, Except.bind] at h_ok
    | ok initial =>
      let ⟨_, h_init_sz, h_init_elem⟩ := update_word_getElem? words bA _ initial h_init
      have h_mid_step : ∃ middle,
          forIn (Std.Legacy.Range.mk (bA + 1) bB 1 (by decide)) middle
            (write_step (if state then UInt64.ofNat wordMask else 0)) = .ok updated ∧
          middle.size = words.size ∧
          ∀ k, middle[k]? =
            if rB ≠ 0 ∧ k = bB then initial[bB]?.map (fun word => setWordRange word.toNat 0 rB state)
            else initial[k]? := by
        cases Classical.em (rB = 0) with
        | inl h_rB_zero =>
          subst h_rB_zero
          simp only [h_init, bne_self_eq_false, Bool.false_eq_true, reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
          exact ⟨initial, h_ok, h_init_sz, fun k => by simp⟩
        | inr h_rB_zero =>
          have h_bne : (rB != 0) = true := bne_iff_ne.mpr h_rB_zero
          simp only [h_init, h_bne, reduceIte, Bind.bind, Except.bind] at h_ok
          cases h_m : update_word initial bB (fun word => setWordRange word.toNat 0 rB state) with
          | error e => simp [h_m] at h_ok
          | ok mid =>
            simp only [h_m] at h_ok
            let ⟨_, h_mid_sz, h_mid_elem⟩ := update_word_getElem? initial bB _ mid h_m
            refine ⟨mid, h_ok, h_mid_sz.trans h_init_sz, fun k => ?_⟩
            rw [h_mid_elem k]
            cases Classical.em (k = bB) with
            | inl hk =>
              rw [if_pos_eq hk, if_pos_eq ⟨h_rB_zero, hk⟩]
            | inr hk =>
              rw [if_neg_eq hk, if_neg_eq (fun h => hk h.2)]
      let ⟨middle, h_loop, h_mid_sz, h_mid_elem⟩ := h_mid_step
      let fillWord : UInt64 := if state then UInt64.ofNat wordMask else 0
      let ⟨h_upd_sz, h_upd_elem⟩ := write_range_getElem? (bA + 1) bB middle fillWord updated h_loop
      refine ⟨h_upd_sz.trans h_mid_sz, fun k bit h_ib h_bit => ?_⟩
      have h_old : words[k]? = some (GetElem.getElem words k h_ib) := Array.getElem?_eq_getElem h_ib
      have h_fill_bit : Nat.testBit fillWord.toNat bit = state := by
        dsimp only [fillWord]
        cases state
        · simp
        · simp only [reduceIte]
          have h_wm : (UInt64.ofNat wordMask).toNat = wordMask := by decide
          rw [h_wm, testBit_wordMask bit h_bit]
      cases Classical.em (bA + 1 ≤ k ∧ k < bB) with
      | inl h_in_mid =>
        refine ⟨fillWord, GetElem.getElem words k h_ib, ?_, h_old, ?_⟩
        · have he := h_upd_elem k
          rw [if_pos_eq h_in_mid] at he
          exact he
        · have h_in_idx : bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB :=
            ⟨mul64_add_le_of_lt_blk h_rA h_in_mid.1, mul64_add_lt_of_lt_blk h_bit h_in_mid.2⟩
          rw [if_pos_eq h_in_idx, h_fill_bit]
      | inr h_in_mid =>
        have he_upd := h_upd_elem k
        rw [if_neg_eq h_in_mid, h_mid_elem k] at he_upd
        cases Classical.em (rB ≠ 0 ∧ k = bB) with
        | inl h_k_bB =>
          let ⟨h_rB_nz, h_eq_bB⟩ := h_k_bB
          subst h_eq_bB
          have h_init_bB : initial[k]? = words[k]? := by
            have hi := h_init_elem k
            have hne : k ≠ bA := Nat.ne_of_gt h_lt_div
            rw [if_neg_eq hne] at hi
            exact hi
          rw [if_pos_eq ⟨h_rB_nz, rfl⟩, h_init_bB, h_old] at he_upd
          refine ⟨setWordRange (GetElem.getElem words k h_ib).toNat 0 rB state,
            GetElem.getElem words k h_ib, he_upd, h_old, ?_⟩
          have h_hi : rB ≤ 64 := Nat.le_of_lt h_rB
          rw [setWordRange_testBit _ 0 rB bit state (Nat.zero_le _) h_hi h_bit]
          have h_iff : (0 ≤ bit ∧ bit < rB) ↔ (bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < k * 64 + rB) :=
            ⟨fun ⟨_, h2⟩ => ⟨mul64_add_le_of_lt_blk h_rA h_lt_div, Nat.add_lt_add_left h2 _⟩,
             fun ⟨_, h2⟩ => ⟨Nat.zero_le _, Nat.lt_of_add_lt_add_left h2⟩⟩
          cases Classical.em (0 ≤ bit ∧ bit < rB) with
          | inl h1 =>
            rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
          | inr h1 =>
            rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
        | inr h_k_bB =>
          rw [if_neg_eq h_k_bB, h_init_elem k] at he_upd
          cases Classical.em (k = bA) with
          | inl h_k_bA =>
            subst h_k_bA
            rw [if_pos_eq rfl, h_old] at he_upd
            refine ⟨setWordRange (GetElem.getElem words k h_ib).toNat rA 64 state,
              GetElem.getElem words k h_ib, he_upd, h_old, ?_⟩
            have h_lo_hi : rA ≤ 64 := Nat.le_of_lt h_rA
            rw [setWordRange_testBit _ rA 64 bit state h_lo_hi (Nat.le_refl 64) h_bit]
            have h_iff : (rA ≤ bit ∧ bit < 64) ↔ (k * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) :=
              ⟨fun ⟨h1, _⟩ => ⟨Nat.add_le_add_left h1 _, mul64_add_lt_of_lt_blk h_bit h_lt_div⟩,
               fun ⟨h1, _⟩ => ⟨Nat.le_of_add_le_add_left h1, h_bit⟩⟩
            cases Classical.em (rA ≤ bit ∧ bit < 64) with
            | inl h1 =>
              rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
            | inr h1 =>
              rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
          | inr h_k_bA =>
            rw [if_neg_eq h_k_bA] at he_upd
            refine ⟨GetElem.getElem words k h_ib, GetElem.getElem words k h_ib, he_upd.trans h_old, h_old, ?_⟩
            have h_out : ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by
              intro ⟨h1, h2⟩
              have h_le_k : bA ≤ k := le_blk_of_mul64_add_le h_bit h1
              have h_succ_le : bA + 1 ≤ k := Nat.lt_of_le_of_ne h_le_k (Ne.symm h_k_bA)
              cases Nat.lt_or_ge k bB with
              | inl hk_lt => exact h_in_mid ⟨h_succ_le, hk_lt⟩
              | inr hk_ge =>
                cases Nat.lt_or_eq_of_le hk_ge with
                | inl h_gt => exact Nat.not_lt_of_le (Nat.le_of_lt (mul64_add_lt_of_lt_blk h_rB h_gt)) h2
                | inr h_eq =>
                  have hrB0 : rB = 0 := Classical.byContradiction fun hnz => h_k_bB ⟨hnz, h_eq.symm⟩
                  subst h_eq hrB0
                  exact Nat.not_lt_zero _ (Nat.lt_of_add_lt_add_left h2)
            rw [if_neg_eq h_out]

/--
On a well-formed mask, `get` succeeds at every in-bounds byte index, for both
the `.Lazy` and the `.Materialized` representation.
-/
theorem get_ok_of_wellFormed (mask : Miri.Memory.InitMask) (idx : Size)
    (valid : Miri.Memory.InitMask.WriteProof.WellFormed mask) (inBounds : idx.bytes.toNat < mask.len.bytes.toNat) :
    ∃ b, mask.get idx = .ok b := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state => exact ⟨state, rfl⟩
    | Materialized blocks =>
      dsimp only [Miri.Memory.InitMask.WriteProof.WellFormed] at valid
      dsimp only at inBounds
      have h_ib : (HDiv.hDiv idx.bytes.toNat 64) < blocks.blocks.size := nat_lt_div_of_lt_mul_64 (Nat.lt_of_lt_of_le inBounds valid)
      refine ⟨Nat.testBit (GetElem.getElem blocks.blocks (HDiv.hDiv idx.bytes.toNat 64) h_ib).toNat
        ((HMod.hMod idx.bytes.toNat 64)), ?_⟩
      rw [Mirrors.InitMask.get_eq_getR]
      unfold Mirrors.InitMask.getR Mirrors.InitMaskMaterialized.get
        Mirrors.InitMaskMaterialized.getBlock
        Mirrors.InitMaskMaterialized.bitIndexR Mirrors.sizeBytes Mirrors.blockSize
        Mirrors.bitAt
      dsimp only
      rw [Array.getElem?_eq_getElem h_ib]
      rfl

/--
Pointwise characterization of `setRange`: after a successful nonempty in-bounds
`mask.setRange range state = .ok updated`, every in-bounds byte in
`[range.start, finish)` reads `state` and every other in-bounds byte reads its
old value. Covers `.Lazy` and `.Materialized` masks, including the `.Lazy` →
`.Materialized` transition and ranges crossing 64-bit word boundaries.
-/
theorem set_range_get (mask updated : Miri.Memory.InitMask) (range : AllocRange) (finish idx : Size)
    (state : Bool)
    (valid : Miri.Memory.InitMask.WriteProof.WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (idxInBounds : idx.bytes.toNat < mask.len.bytes.toNat)
    (h_set : mask.setRange range state = .ok updated) :
    updated.get idx =
      if range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat then
        .ok state
      else
        mask.get idx := by
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds idxInBounds
    cases blocks with
    | Materialized oldBlocks =>
      dsimp only [Miri.Memory.InitMask.WriteProof.WellFormed] at valid
      rw [Mirrors.InitMask.setRange_eq_R] at h_set
      unfold Mirrors.InitMask.setRangeR at h_set
      simp only [endpoint, Bind.bind, Except.bind] at h_set
      cases Classical.em (range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes) with
      | inl full =>
        rw [if_pos_eq full] at h_set
        injection h_set with h_upd
        subst h_upd
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat :=
          ⟨by simp [full.1], Nat.lt_of_lt_of_le idxInBounds (UInt64.le_iff_toNat_le.mp full.2)⟩
        rw [if_pos_eq h_in]
        rfl
      | inr full =>
        rw [if_neg_eq full] at h_set
        have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
        rw [if_pos_eq h_fin_le] at h_set
        have h_red := set_range_inbounds_reduces oldBlocks range.start finish state
        unfold setRangeInbounds at h_red
        rw [h_red] at h_set
        cases h_words : set_range_words oldBlocks.blocks
            ((HDiv.hDiv range.start.bytes.toNat 64)) ((HMod.hMod range.start.bytes.toNat 64))
            ((HDiv.hDiv finish.bytes.toNat 64)) ((HMod.hMod finish.bytes.toNat 64)) state with
        | error e => simp [h_words, Bind.bind, Except.bind] at h_set
        | ok newWords =>
          simp only [h_words, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
          subst h_set
          have h_rA : (HMod.hMod range.start.bytes.toNat 64) < 64 := Nat.mod_lt _ (by decide)
          have h_rB : (HMod.hMod finish.bytes.toNat 64) < 64 := Nat.mod_lt _ (by decide)
          have h_ne_mul : ((HDiv.hDiv range.start.bytes.toNat 64)) * 64 + (HMod.hMod range.start.bytes.toNat 64) <
              ((HDiv.hDiv finish.bytes.toNat 64)) * 64 + (HMod.hMod finish.bytes.toNat 64) := by
            rw [div_mul_64_add_mod, div_mul_64_add_mod]; exact nonempty
          let ⟨_, h_bit⟩ := set_range_words_bit_gen oldBlocks.blocks _ _ _ _ state newWords
            h_rA h_rB h_ne_mul h_words
          have h_ib : (HDiv.hDiv idx.bytes.toNat 64) < oldBlocks.blocks.size :=
            nat_lt_div_of_lt_mul_64 (Nat.lt_of_lt_of_le idxInBounds valid)
          let ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit ((HDiv.hDiv idx.bytes.toNat 64)) ((HMod.hMod idx.bytes.toNat 64))
            h_ib (Nat.mod_lt _ (by decide))
          have h_iff : (((HDiv.hDiv range.start.bytes.toNat 64)) * 64 + (HMod.hMod range.start.bytes.toNat 64) ≤
                ((HDiv.hDiv idx.bytes.toNat 64)) * 64 + (HMod.hMod idx.bytes.toNat 64) ∧
              ((HDiv.hDiv idx.bytes.toNat 64)) * 64 + (HMod.hMod idx.bytes.toNat 64) <
                ((HDiv.hDiv finish.bytes.toNat 64)) * 64 + (HMod.hMod finish.bytes.toNat 64)) ↔
              (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) := by
            rw [div_mul_64_add_mod, div_mul_64_add_mod, div_mul_64_add_mod]
          rw [Mirrors.InitMask.get_eq_getR]
          unfold Mirrors.InitMask.getR Mirrors.InitMaskMaterialized.get
            Mirrors.InitMaskMaterialized.getBlock
            Mirrors.InitMaskMaterialized.bitIndexR Mirrors.sizeBytes Mirrors.blockSize
            Mirrors.bitAt
          dsimp only
          rw [hw, holdW]
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [h_tb]
          cases Classical.em (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) with
          | inl h_in =>
            rw [if_pos_eq (h_iff.mpr h_in), if_pos_eq h_in]
          | inr h_in =>
            rw [if_neg_eq (fun h => h_in (h_iff.mp h)), if_neg_eq h_in]
    | Lazy initial =>
      rw [Mirrors.InitMask.setRange_eq_R] at h_set
      unfold Mirrors.InitMask.setRangeR at h_set
      simp only [endpoint, Bind.bind, Except.bind] at h_set
      cases Classical.em (range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes) with
      | inl full =>
        rw [if_pos_eq full] at h_set
        injection h_set with h_upd
        subst h_upd
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat :=
          ⟨by simp [full.1], Nat.lt_of_lt_of_le idxInBounds (UInt64.le_iff_toNat_le.mp full.2)⟩
        rw [if_pos_eq h_in]
        rfl
      | inr full =>
        rw [if_neg_eq full] at h_set
        cases Classical.em (initial == state) with
        | inl same =>
          have h_eq_st : initial = state := eq_of_beq same
          subst h_eq_st
          rw [if_pos_eq (beq_self_eq_true initial)] at h_set
          have notGrow : ¬finish.bytes > len.bytes := by
            have _h_simpa := Nat.not_lt.mpr inBounds
            simp at _h_simpa
            simp [UInt64.lt_iff_toNat_lt]
            exact _h_simpa
          rw [if_neg_eq notGrow] at h_set
          injection h_set with h_upd
          subst h_upd
          cases Classical.em (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) with
          | inl h_in =>
            rw [if_pos_eq h_in]; rfl
          | inr h_in =>
            rw [if_neg_eq h_in]
        | inr same =>
          rw [if_neg_eq same] at h_set
          have lenNonzero : len.bytes.toNat ≠ 0 :=
            Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le _) nonempty) inBounds)
          have matEq := materialize_lazy_nonzero len initial lenNonzero
          unfold materialize Miri.Memory.InitMask.new at matEq
          rw [matEq] at h_set
          have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
          dsimp only at h_set
          rw [if_pos_eq h_fin_le] at h_set
          let initWords := Array.replicate ((HDiv.hDiv len.bytes.toNat 64) + 1)
            (if initial then UInt64.ofNat 18446744073709551615 else 0)
          have h_red := set_range_inbounds_reduces ⟨initWords⟩ range.start finish state
          unfold setRangeInbounds at h_red
          dsimp only [initWords] at h_red
          rw [h_red] at h_set
          cases h_words : set_range_words initWords
              ((HDiv.hDiv range.start.bytes.toNat 64)) ((HMod.hMod range.start.bytes.toNat 64))
              ((HDiv.hDiv finish.bytes.toNat 64)) ((HMod.hMod finish.bytes.toNat 64)) state with
          | error e =>
            dsimp only [initWords] at h_words
            rw [h_words] at h_set
            cases h_set
          | ok newWords =>
            have h_words_unf := h_words
            dsimp only [initWords] at h_words_unf
            rw [h_words_unf] at h_set
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
            subst h_set
            have h_rA : (HMod.hMod range.start.bytes.toNat 64) < 64 := Nat.mod_lt _ (by decide)
            have h_rB : (HMod.hMod finish.bytes.toNat 64) < 64 := Nat.mod_lt _ (by decide)
            have h_ne_mul : ((HDiv.hDiv range.start.bytes.toNat 64)) * 64 + (HMod.hMod range.start.bytes.toNat 64) <
                ((HDiv.hDiv finish.bytes.toNat 64)) * 64 + (HMod.hMod finish.bytes.toNat 64) := by
              rw [div_mul_64_add_mod, div_mul_64_add_mod]; exact nonempty
            let ⟨_, h_bit⟩ := set_range_words_bit_gen initWords _ _ _ _ state newWords
              h_rA h_rB h_ne_mul h_words
            have h_ib_len : (HDiv.hDiv idx.bytes.toNat 64) < (HDiv.hDiv len.bytes.toNat 64) + 1 :=
              Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt idxInBounds))
            have h_ib : (HDiv.hDiv idx.bytes.toNat 64) < initWords.size := by
              simp only [initWords, Array.size_replicate]; exact h_ib_len
            let ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit ((HDiv.hDiv idx.bytes.toNat 64)) ((HMod.hMod idx.bytes.toNat 64))
              h_ib (Nat.mod_lt _ (by decide))
            have h_oldW_eq : oldW = (if initial then UInt64.ofNat 18446744073709551615 else 0) := by
              have h_rep : initWords[(HDiv.hDiv idx.bytes.toNat 64)]? =
                  some (if initial then UInt64.ofNat 18446744073709551615 else 0) := by
                simp [initWords, h_ib_len]
              exact Option.some.inj (holdW.symm.trans h_rep)
            have h_old_bit : Nat.testBit oldW.toNat ((HMod.hMod idx.bytes.toNat 64)) = initial := by
              rw [h_oldW_eq]
              cases initial
              · simp
              · simp only [reduceIte]
                have h_wm : (UInt64.ofNat 18446744073709551615).toNat = wordMask := by decide
                rw [h_wm, testBit_wordMask _ (Nat.mod_lt _ (by decide))]
            have h_iff : (((HDiv.hDiv range.start.bytes.toNat 64)) * 64 + (HMod.hMod range.start.bytes.toNat 64) ≤
                  ((HDiv.hDiv idx.bytes.toNat 64)) * 64 + (HMod.hMod idx.bytes.toNat 64) ∧
                ((HDiv.hDiv idx.bytes.toNat 64)) * 64 + (HMod.hMod idx.bytes.toNat 64) <
                  ((HDiv.hDiv finish.bytes.toNat 64)) * 64 + (HMod.hMod finish.bytes.toNat 64)) ↔
                (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) := by
              rw [div_mul_64_add_mod, div_mul_64_add_mod, div_mul_64_add_mod]
            rw [Mirrors.InitMask.get_eq_getR]
            unfold Mirrors.InitMask.getR Mirrors.InitMaskMaterialized.get
              Mirrors.InitMaskMaterialized.getBlock
              Mirrors.InitMaskMaterialized.bitIndexR Mirrors.sizeBytes Mirrors.blockSize
              Mirrors.bitAt
            dsimp only
            rw [hw]
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
            rw [h_tb, h_old_bit]
            cases Classical.em (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) with
            | inl h_in =>
              rw [if_pos_eq (h_iff.mpr h_in), if_pos_eq h_in]
            | inr h_in =>
              rw [if_neg_eq (fun h => h_in (h_iff.mp h)), if_neg_eq h_in]

private theorem firstSetBit_spec_none (bits startBit : Nat) :
    Mirrors.InitMaskMaterialized.firstSetBit bits startBit = none ↔
      ∀ b, startBit ≤ b → b < 64 → Nat.testBit bits b = false := by
  unfold Mirrors.InitMaskMaterialized.firstSetBit Mirrors.bitAt
  simp only [Option.map_eq_none_iff, List.find?_eq_none, List.mem_range, Bool.not_eq_true]
  constructor
  · intro h b h_lo h_hi
    have h_off : b - startBit < 64 - startBit := Nat.sub_lt_sub_right h_lo h_hi
    have h_eq : startBit + (b - startBit) = b := Nat.add_sub_of_le h_lo
    have _h_simpa := h (b - startBit) h_off
    simp [h_eq] at _h_simpa
    exact _h_simpa
  · intro h off h_off
    exact h (startBit + off) (Nat.le_add_right startBit off) (add_lt_of_lt_sub_left h_off)

private theorem firstSetBit_spec_some (bits startBit res : Nat)
    (h_some : Mirrors.InitMaskMaterialized.firstSetBit bits startBit = some res) :
    startBit ≤ res ∧ res < 64 ∧ Nat.testBit bits res = true ∧
      ∀ b, startBit ≤ b → b < res → Nat.testBit bits b = false := by
  unfold Mirrors.InitMaskMaterialized.firstSetBit Mirrors.bitAt at h_some
  rw [Option.map_eq_some_iff] at h_some
  let ⟨off, h_find, _heq_1⟩ := h_some
  subst _heq_1
  have h_mem : off ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some h_find
  rw [List.mem_range] at h_mem
  let ⟨h_true, xs, ys, h_eq_list, h_all_false⟩ := List.find?_eq_some_iff_append.mp h_find
  have h_res_lt : off + startBit < 64 := Nat.add_lt_of_lt_sub h_mem
  refine ⟨Nat.le_add_left startBit off, h_res_lt,
    by rw [Nat.add_comm]; exact h_true, fun b h_lo h_lt => ?_⟩
  have h_pw : List.Pairwise (· < ·) (List.range (64 - startBit)) := List.pairwise_lt_range
  rw [h_eq_list, List.pairwise_append, List.pairwise_cons] at h_pw
  let ⟨_, ⟨h_lt_ys, _⟩, _⟩ := h_pw
  have h_b_lt64 : b < 64 := Nat.lt_trans h_lt h_res_lt
  have h_b_mem : b - startBit ∈ List.range (64 - startBit) := by
    rw [List.mem_range]; exact Nat.sub_lt_sub_right h_lo h_b_lt64
  rw [h_eq_list, List.mem_append, List.mem_cons] at h_b_mem
  cases h_b_mem with
  | inl h_in_xs =>
    have hf := h_all_false (b - startBit) h_in_xs
    have h_sum : startBit + (b - startBit) = b := Nat.add_sub_of_le h_lo
    have _h := hf
    simp [h_sum] at _h
    exact _h
  | inr h_rest =>
    have h_sub_lt : b - startBit < off := Nat.sub_lt_left_of_lt_add h_lo (by rw [Nat.add_comm]; exact h_lt)
    cases h_rest with
    | inl h_eq_off => exact absurd h_eq_off (Nat.ne_of_lt h_sub_lt)
    | inr h_in_ys => exact absurd (h_lt_ys (b - startBit) h_in_ys) (Nat.not_lt_of_le (Nat.le_of_lt h_sub_lt))

private theorem testBit_wordMask_sub (w : UInt64) (bit : Nat) (h_bit : bit < 64) :
    Nat.testBit (wordMask - w.toNat) bit = !Nat.testBit w.toNat bit := by
  have h_wm : wordMask = (HPow.hPow (2 : Nat) 64) - 1 := by decide
  rw [h_wm]
  have h_lt := w.toNat_lt
  have h_bv : BitVec.ofNat 64 ((HPow.hPow (2 : Nat) 64) - 1 - w.toNat) = Complement.complement (BitVec.ofNat 64 w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    have h_sub_lt : HPow.hPow (2 : Nat) 64 - 1 - w.toNat < HPow.hPow (2 : Nat) 64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos 64) Nat.zero_lt_one)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_sub_lt, BitVec.toNat_not,
      Nat.mod_eq_of_lt h_lt]
  have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
  exact h1

private theorem searchBlock_spec (word : UInt64) (block startBit : Nat) (isInit : Bool)
    (h_block_fits : block * 64 + 63 ≤ 18446744073709551615) :
    ∃ res?, Mirrors.InitMaskMaterialized.searchBlock word block startBit isInit = .ok res? ∧
      match res? with
      | none => ∀ b, startBit ≤ b → b < 64 → Nat.testBit word.toNat b = !isInit
      | some idx =>
        ∃ bit, startBit ≤ bit ∧ bit < 64 ∧ idx.bytes.toNat = block * 64 + bit ∧
          Nat.testBit word.toNat bit = isInit ∧
          ∀ b, startBit ≤ b → b < bit → Nat.testBit word.toNat b = !isInit := by
  let bits := if isInit then word.toNat else wordMask - word.toNat
  have h_bits_tb : ∀ b, b < 64 → (Nat.testBit bits b = true ↔ Nat.testBit word.toNat b = isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, reduceIte]
      rw [testBit_wordMask_sub word b hb]
      cases word.toNat.testBit b <;> simp
    · simp
  have h_bits_false : ∀ b, b < 64 → (Nat.testBit bits b = false ↔ Nat.testBit word.toNat b = !isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, reduceIte, Bool.not_false]
      rw [testBit_wordMask_sub word b hb]
      cases word.toNat.testBit b <;> simp
    · simp
  cases h_fsb : Mirrors.InitMaskMaterialized.firstSetBit bits startBit with
  | none =>
    refine ⟨none, ?_, ?_⟩
    · unfold Mirrors.InitMaskMaterialized.searchBlock
      dsimp only [bits] at h_fsb
      unfold wordMask at h_fsb
      simp [h_fsb, Pure.pure, Except.pure]
    · intro b h_lo h_hi
      have hf := (firstSetBit_spec_none bits startBit).mp h_fsb b h_lo h_hi
      exact (h_bits_false b h_hi).mp hf
  | some bit =>
    let ⟨h_lo, h_hi, h_tb, h_prev⟩ := firstSetBit_spec_some bits startBit bit h_fsb
    have h_fits : block * 64 + bit ≤ Mirrors.maxSizeBytes := by
      unfold Mirrors.maxSizeBytes
      exact Nat.le_trans (Nat.add_le_add_left (Nat.le_pred_of_lt h_hi) _) h_block_fits
    have h_lt264 : block * 64 + bit < (HPow.hPow (2 : Nat) 64) :=
      Nat.lt_of_le_of_lt h_fits (by unfold Mirrors.maxSizeBytes; decide)
    let idx := Size.ofBytes (UInt64.ofNat (block * 64 + bit))
    have h_sfi : Mirrors.InitMaskMaterialized.sizeFromBitIndex block bit = .ok idx := by
      unfold Mirrors.InitMaskMaterialized.sizeFromBitIndex Mirrors.sizeFromNat Mirrors.blockSize
      rw [if_pos_eq h_fits]
    refine ⟨some idx, ?_, bit, h_lo, h_hi, ?_, (h_bits_tb bit h_hi).mp h_tb, ?_⟩
    · unfold Mirrors.InitMaskMaterialized.searchBlock
      dsimp only [bits] at h_fsb
      unfold wordMask at h_fsb
      simp [h_fsb, h_sfi, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [idx, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_lt264]
    · intro b hb_lo hb_lt
      exact (h_bits_false b (Nat.lt_trans hb_lt h_hi)).mp (h_prev b hb_lo hb_lt)

private theorem search_blocks_list_spec (self : InitMaskMaterialized) (finish : Size) (isInit : Bool)
    (blocksList : List Nat)
    (h_sorted : List.Pairwise (· < ·) blocksList)
    (h_blocks_in : ∀ blk, blk ∈ blocksList → blk < self.blocks.size)
    (h_blocks_fits : ∀ blk, blk ∈ blocksList → blk * 64 + 63 ≤ 18446744073709551615) :
    ∃ out,
      forIn blocksList (none, Unit.unit) (fun (block : Nat) (_ : Option (Option Size) × Unit) =>
        (Bind.bind (getBlock self block) fun w =>
          Bind.bind (Mirrors.InitMaskMaterialized.searchBlock w block 0 isInit) fun
          | some index =>
            if Mirrors.sizeBytes index < Mirrors.sizeBytes finish then
              Pure.pure (ForInStep.done (some (some index), ⟨⟩))
            else
              Pure.pure (ForInStep.done (some none, ⟨⟩))
          | none => Pure.pure (ForInStep.yield (none, ⟨⟩)) :
          Except InitMaskError (ForInStep (Option (Option Size) × PUnit)))) = .ok (out, ⟨⟩) ∧
      match out with
      | none | some none =>
        ∀ blk (h_mem : blk ∈ blocksList) (b : Nat), b < 64 → blk * 64 + b < finish.bytes.toNat →
          Nat.testBit (GetElem.getElem self.blocks blk (h_blocks_in blk h_mem)).toNat b = !isInit
      | some (some idx) =>
        ∃ blk, ∃ (h_mem : blk ∈ blocksList), ∃ bit, bit < 64 ∧
          idx.bytes.toNat = blk * 64 + bit ∧
          idx.bytes.toNat < finish.bytes.toNat ∧
          Nat.testBit (GetElem.getElem self.blocks blk (h_blocks_in blk h_mem)).toNat bit = isInit ∧
          ∀ blk' (h_mem' : blk' ∈ blocksList) (b : Nat), b < 64 →
            blk' * 64 + b < idx.bytes.toNat →
            Nat.testBit (GetElem.getElem self.blocks blk' (h_blocks_in blk' h_mem')).toNat b = !isInit := by
  induction blocksList with
  | nil =>
    refine ⟨none, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons blk rest ih =>
    rw [List.pairwise_cons] at h_sorted
    let ⟨h_lt_rest, h_pw_rest⟩ := h_sorted
    have h_ib : blk < self.blocks.size := h_blocks_in blk (List.mem_cons_self)
    have h_fits : blk * 64 + 63 ≤ 18446744073709551615 := h_blocks_fits blk (List.mem_cons_self)
    have h_gb : getBlock self blk = .ok (GetElem.getElem self.blocks blk h_ib) := get_block_ok self.blocks blk h_ib
    let ⟨res?, h_sb, h_sb_prop⟩ := searchBlock_spec (GetElem.getElem self.blocks blk h_ib) blk 0 isInit h_fits
    cases res? with
    | none =>
      let ⟨tailOut, h_tail, h_tail_prop⟩ := ih h_pw_rest
        (fun x hx => h_blocks_in x (List.mem_cons_of_mem _ hx))
        (fun x hx => h_blocks_fits x (List.mem_cons_of_mem _ hx))
      refine ⟨tailOut, ?_, ?_⟩
      · simp only [List.forIn_cons, h_gb, h_sb, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact h_tail
      · cases tailOut with
        | none =>
          intro x hx b hb h_lt_fin
          cases List.mem_cons.mp hx with
          | inl _heq =>
            subst _heq
            exact h_sb_prop b (Nat.zero_le _) hb
          | inr hx_rest =>
            exact h_tail_prop x hx_rest b hb h_lt_fin
        | some inner =>
          cases inner with
          | none =>
            intro x hx b hb h_lt_fin
            cases List.mem_cons.mp hx with
            | inl _heq =>
              subst _heq
              exact h_sb_prop b (Nat.zero_le _) hb
            | inr hx_rest =>
              exact h_tail_prop x hx_rest b hb h_lt_fin
          | some idx =>
            let ⟨x, hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, h_prev_rest⟩ := h_tail_prop
            refine ⟨x, List.mem_cons_of_mem _ hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, ?_⟩
            intro x' hx' b hb h_lt_idx
            cases List.mem_cons.mp hx' with
            | inl _heq =>
              subst _heq
              exact h_sb_prop b (Nat.zero_le _) hb
            | inr hx'_rest =>
              exact h_prev_rest x' hx'_rest b hb h_lt_idx
    | some idx =>
      let ⟨bit, _, hbit, h_idx_eq, h_tb, h_prev⟩ := h_sb_prop
      cases Classical.em (Mirrors.sizeBytes idx < Mirrors.sizeBytes finish) with
      | inl h_lt_fin =>
        refine ⟨some (some idx), ?_, blk, List.mem_cons_self, bit, hbit, h_idx_eq, ?_, h_tb, ?_⟩
        · simp [List.forIn_cons, h_gb, h_sb, h_lt_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have _h := h_lt_fin; simp [Mirrors.sizeBytes] at _h; simp; exact _h
        · intro x' hx' b hb h_lt_idx
          cases List.mem_cons.mp hx' with
          | inl _heq =>
            subst _heq
            exact h_prev b (Nat.zero_le _) (Nat.lt_of_add_lt_add_left (by rw [← h_idx_eq]; exact h_lt_idx))
          | inr hx'_rest =>
            exact absurd (mul64_add_lt_of_lt_blk hbit (h_lt_rest x' hx'_rest))
              (Nat.not_lt_of_le (Nat.le_of_lt (by rw [← h_idx_eq]; exact h_lt_idx)))
      | inr h_lt_fin =>
        refine ⟨some none, ?_, ?_⟩
        · simp [List.forIn_cons, h_gb, h_sb, h_lt_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have h_ge_fin : finish.bytes.toNat ≤ blk * 64 + bit := by
            simp only [Mirrors.sizeBytes] at h_lt_fin
            rw [← h_idx_eq]
            exact Nat.le_of_not_lt h_lt_fin
          intro x hx b hb h_lt
          have h_lt_blk : x * 64 + b < blk * 64 + bit := Nat.lt_of_lt_of_le h_lt h_ge_fin
          cases List.mem_cons.mp hx with
          | inl _heq =>
            subst _heq
            exact h_prev b (Nat.zero_le _) (Nat.lt_of_add_lt_add_left h_lt_blk)
          | inr hx_rest =>
            exact absurd (mul64_add_lt_of_lt_blk hbit (h_lt_rest x hx_rest))
              (Nat.not_lt_of_le (Nat.le_of_lt h_lt_blk))

private theorem findBit_spec (self : InitMaskMaterialized) (start finish : Size) (isInit : Bool)
    (h_cap : finish.bytes.toNat ≤ self.blocks.size * 64) :
    ∃ res?, Mirrors.InitMaskMaterialized.findBit self start finish isInit = .ok res? ∧
      match res? with
      | none =>
        ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
          Mirrors.InitMaskMaterialized.get self idx = .ok (!isInit)
      | some found =>
        start.bytes.toNat ≤ found.bytes.toNat ∧ found.bytes.toNat < finish.bytes.toNat ∧
          Mirrors.InitMaskMaterialized.get self found = .ok isInit ∧
          ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < found.bytes.toNat →
            Mirrors.InitMaskMaterialized.get self idx = .ok (!isInit) := by
  unfold Mirrors.InitMaskMaterialized.findBit
    Mirrors.InitMaskMaterialized.findBitFast
  have h_fin_u64 := finish.bytes.toNat_lt
  cases Classical.em (Mirrors.sizeBytes start ≥ Mirrors.sizeBytes finish) with
  | inl h_empty =>
    refine ⟨none, ?_, ?_⟩
    · simp [h_empty, Pure.pure, Except.pure]
    · intro idx h1 h2
      simp only [Mirrors.sizeBytes] at h_empty
      exact absurd h2 (Nat.not_lt_of_le (Nat.le_trans h_empty h1))
  | inr h_empty =>
    rw [if_neg_eq h_empty]
    have h_lt_sf : start.bytes.toNat < finish.bytes.toNat := by
      simp only [Mirrors.sizeBytes] at h_empty
      exact Nat.lt_of_not_le h_empty
    let startBlock := (HDiv.hDiv start.bytes.toNat 64)
    let startBit := (HMod.hMod start.bytes.toNat 64)
    let endIncNat := finish.bytes.toNat - 1
    have h_end_lt264 : endIncNat < HPow.hPow (2 : Nat) 64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_fin_u64
    have h_end_fits : endIncNat ≤ Mirrors.maxSizeBytes :=
      Mirrors.le_maxSizeBytes_of_lt h_end_lt264
    have h_sfn : Mirrors.sizeFromNat (finish.bytes.toNat - 1) =
        .ok (Size.ofBytes (UInt64.ofNat endIncNat)) := by
      unfold Mirrors.sizeFromNat
      dsimp only [endIncNat] at h_end_fits
      dsimp only [endIncNat]
      rw [if_pos_eq h_end_fits]
    have h_endInc_bytes : (Size.ofBytes (UInt64.ofNat endIncNat)).bytes.toNat = endIncNat := by
      simp [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_end_lt264]
    let endBlock := (HDiv.hDiv endIncNat 64)
    have h_sb_ib : startBlock < self.blocks.size :=
      nat_lt_div_of_lt_mul_64 (Nat.lt_of_lt_of_le h_lt_sf h_cap)
    have h_fin_pos : 0 < finish.bytes.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt_sf
    have h_eb_ib : endBlock < self.blocks.size :=
      nat_lt_div_of_lt_mul_64 (Nat.lt_of_lt_of_le (Nat.sub_lt h_fin_pos Nat.zero_lt_one) h_cap)
    have h_sb_fits : startBlock * 64 + 63 ≤ 18446744073709551615 := by
      have h_sb_le : startBlock ≤ HDiv.hDiv 18446744073709551615 64 :=
        Nat.div_le_div_right (Nat.le_pred_of_lt start.bytes.toNat_lt)
      exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 64 h_sb_le) 63) (by decide)
    have h_gb0 : Mirrors.InitMaskMaterialized.getBlock self startBlock =
        .ok (GetElem.getElem self.blocks startBlock h_sb_ib) :=
      get_block_ok self.blocks startBlock h_sb_ib
    let ⟨first?, h_sb0, h_sb0_prop⟩ :=
      searchBlock_spec (GetElem.getElem self.blocks startBlock h_sb_ib) startBlock startBit isInit h_sb_fits
    have h_get_eq : ∀ (idx : Size) (h_ib : (HDiv.hDiv idx.bytes.toNat 64) < self.blocks.size),
        Mirrors.InitMaskMaterialized.get self idx =
          .ok (Nat.testBit (GetElem.getElem self.blocks (HDiv.hDiv idx.bytes.toNat 64) h_ib).toNat
            ((HMod.hMod idx.bytes.toNat 64))) := by
      intro idx h_ib
      unfold Mirrors.InitMaskMaterialized.get Mirrors.InitMaskMaterialized.getBlock
        Mirrors.InitMaskMaterialized.bitIndexR Mirrors.sizeBytes Mirrors.blockSize Mirrors.bitAt
      dsimp only
      rw [Array.getElem?_eq_getElem h_ib]
      rfl
    simp only [Mirrors.InitMaskMaterialized.bitIndexR, Mirrors.sizeBytes, Mirrors.blockSize]
    rw [h_sfn]
    simp only [Bind.bind, Except.bind, h_endInc_bytes]
    dsimp only [startBlock, startBit, endBlock] at h_gb0 h_sb0
    rw [h_gb0]
    simp only
    rw [h_sb0]
    simp only
    cases first? with
    | some firstIdx =>
      let ⟨bit, h_lo, h_hi, h_f_eq, h_tb, h_prev⟩ := h_sb0_prop
      cases Classical.em (firstIdx.bytes.toNat < finish.bytes.toNat) with
      | inl h_lt_f =>
        refine ⟨some firstIdx, ?_, ?_⟩
        · simp [h_lt_f, Pure.pure, Except.pure]
        · have ⟨h_div, h_mod⟩ := div_mod_64_of_eq h_hi h_f_eq
          have h_s_le_f : start.bytes.toNat ≤ firstIdx.bytes.toNat := by
            rw [← div_mul_64_add_mod start.bytes.toNat, h_f_eq]
            exact Nat.add_le_add_left h_lo _
          refine ⟨h_s_le_f, h_lt_f, ?_, ?_⟩
          · rw [h_get_eq firstIdx (by rw [h_div]; exact h_sb_ib)]
            have _h_simpa := h_tb
            simp [h_div, h_mod]
            exact _h_simpa
          · intro idx h_idx_lo h_idx_lt
            have h_idx_div : (HDiv.hDiv idx.bytes.toNat 64) = startBlock :=
              Nat.le_antisymm (by rw [← h_div]; exact Nat.div_le_div_right (Nat.le_of_lt h_idx_lt))
                (Nat.div_le_div_right h_idx_lo)
            rw [h_get_eq idx (by rw [h_idx_div]; exact h_sb_ib)]
            have h_idx_ge_sb : startBit ≤ HMod.hMod idx.bytes.toNat 64 := by
              have h_le' : startBlock * 64 + startBit ≤ startBlock * 64 + HMod.hMod idx.bytes.toNat 64 := by
                rw [div_mul_64_add_mod start.bytes.toNat, ← h_idx_div, div_mul_64_add_mod idx.bytes.toNat]
                exact h_idx_lo
              exact Nat.le_of_add_le_add_left h_le'
            have h_idx_lt_bit : HMod.hMod idx.bytes.toNat 64 < bit := by
              have h_lt' : startBlock * 64 + HMod.hMod idx.bytes.toNat 64 < startBlock * 64 + bit := by
                rw [← h_f_eq, ← h_idx_div, div_mul_64_add_mod idx.bytes.toNat]
                exact h_idx_lt
              exact Nat.lt_of_add_lt_add_left h_lt'
            have h_p := h_prev ((HMod.hMod idx.bytes.toNat 64)) h_idx_ge_sb h_idx_lt_bit
            have _h_simpa := h_p
            simp [h_idx_div]
            exact _h_simpa
      | inr h_lt_f =>
        have ⟨h_div, _⟩ := div_mod_64_of_eq h_hi h_f_eq
        have h_fin_le_f : finish.bytes.toNat ≤ firstIdx.bytes.toNat := Nat.le_of_not_lt h_lt_f
        refine ⟨none, ?_, ?_⟩
        · simp [h_lt_f, Pure.pure, Except.pure]
        · intro idx h_idx_lo h_idx_lt
          have h_idx_lt_f : idx.bytes.toNat < firstIdx.bytes.toNat := Nat.lt_of_lt_of_le h_idx_lt h_fin_le_f
          have h_idx_div : (HDiv.hDiv idx.bytes.toNat 64) = startBlock :=
            Nat.le_antisymm (by rw [← h_div]; exact Nat.div_le_div_right (Nat.le_of_lt h_idx_lt_f))
              (Nat.div_le_div_right h_idx_lo)
          rw [h_get_eq idx (by rw [h_idx_div]; exact h_sb_ib)]
          have h_idx_ge_sb : startBit ≤ HMod.hMod idx.bytes.toNat 64 := by
            have h_le' : startBlock * 64 + startBit ≤ startBlock * 64 + HMod.hMod idx.bytes.toNat 64 := by
              rw [div_mul_64_add_mod start.bytes.toNat, ← h_idx_div, div_mul_64_add_mod idx.bytes.toNat]
              exact h_idx_lo
            exact Nat.le_of_add_le_add_left h_le'
          have h_idx_lt_bit : HMod.hMod idx.bytes.toNat 64 < bit := by
            have h_lt' : startBlock * 64 + HMod.hMod idx.bytes.toNat 64 < startBlock * 64 + bit := by
              rw [← h_f_eq, ← h_idx_div, div_mul_64_add_mod idx.bytes.toNat]
              exact h_idx_lt_f
            exact Nat.lt_of_add_lt_add_left h_lt'
          have h_p := h_prev ((HMod.hMod idx.bytes.toNat 64)) h_idx_ge_sb h_idx_lt_bit
          have _h_simpa := h_p
          simp [h_idx_div]
          exact _h_simpa
    | none =>
      cases Classical.em (startBlock < endBlock) with
      | inl h_more =>
        dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [if_pos_eq h_more]
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        let rngList := List.range'
          (Std.Legacy.Range.mk (startBlock + 1) (endBlock + 1) 1 Nat.zero_lt_one).start
          (Std.Legacy.Range.mk (startBlock + 1) (endBlock + 1) 1 Nat.zero_lt_one).size
          (Std.Legacy.Range.mk (startBlock + 1) (endBlock + 1) 1 Nat.zero_lt_one).step
        have h_mem_rng : ∀ x, x ∈ rngList ↔ (startBlock + 1 ≤ x ∧ x ≤ endBlock) := by
          intro x
          simp only [rngList, List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul]
          constructor
          · intro ⟨i, hi, _heq⟩; subst _heq
            exact ⟨Nat.le_add_right _ _, Nat.le_of_lt_succ (add_lt_of_lt_sub_left hi)⟩
          · intro ⟨h1, h2⟩
            exact ⟨x - (startBlock + 1), Nat.sub_lt_sub_right h1 (Nat.lt_succ_of_le h2),
              (Nat.add_sub_of_le h1).symm⟩
        have h_pw_rng : List.Pairwise (· < ·) rngList := List.pairwise_lt_range'
        have h_in_rng : ∀ x, x ∈ rngList → x < self.blocks.size := by
          intro x hx
          exact Nat.lt_of_le_of_lt ((h_mem_rng x).mp hx).2 h_eb_ib
        have h_eb_le : endBlock ≤ HDiv.hDiv 18446744073709551615 64 := Nat.div_le_div_right h_end_fits
        have h_fits_rng : ∀ x, x ∈ rngList → x * 64 + 63 ≤ 18446744073709551615 := by
          intro x hx
          have hx_le := Nat.le_trans ((h_mem_rng x).mp hx).2 h_eb_le
          exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 64 hx_le) 63) (by decide)
        let ⟨loopOut, h_loop, h_loop_prop⟩ := search_blocks_list_spec self finish isInit
          rngList h_pw_rng h_in_rng h_fits_rng
        unfold Mirrors.sizeBytes at h_loop
        unfold Mirrors.sizeBytes
        dsimp only [rngList, startBlock, endBlock, endIncNat] at h_loop
        dsimp only [rngList, startBlock, endBlock, endIncNat]
        simp only [Bind.bind, Except.bind] at h_loop
        rw [h_loop]
        simp only [Pure.pure, Except.pure]
        cases loopOut with
        | none =>
          refine ⟨none, rfl, ?_⟩
          intro idx h_idx_lo h_idx_lt
          cases Classical.em ((HDiv.hDiv idx.bytes.toNat 64) = startBlock) with
          | inl hk =>
            rw [h_get_eq idx (by rw [hk]; exact h_sb_ib)]
            have h_idx_ge_sb : startBit ≤ HMod.hMod idx.bytes.toNat 64 := by
              have h_le' : startBlock * 64 + startBit ≤ startBlock * 64 + HMod.hMod idx.bytes.toNat 64 := by
                rw [div_mul_64_add_mod start.bytes.toNat, ← hk, div_mul_64_add_mod idx.bytes.toNat]
                exact h_idx_lo
              exact Nat.le_of_add_le_add_left h_le'
            have h_p := h_sb0_prop ((HMod.hMod idx.bytes.toNat 64)) h_idx_ge_sb (Nat.mod_lt _ (by decide))
            have _h_simpa := h_p
            simp [hk]
            exact _h_simpa
          | inr hk =>
            have h_in_l : (HDiv.hDiv idx.bytes.toNat 64) ∈ rngList :=
              (h_mem_rng _).mpr ⟨Nat.lt_of_le_of_ne (Nat.div_le_div_right h_idx_lo) (Ne.symm hk),
                Nat.div_le_div_right (Nat.le_pred_of_lt h_idx_lt)⟩
            rw [h_get_eq idx (h_in_rng _ h_in_l)]
            exact congrArg Except.ok
              (h_loop_prop ((HDiv.hDiv idx.bytes.toNat 64)) h_in_l ((HMod.hMod idx.bytes.toNat 64))
                (Nat.mod_lt _ (by decide)) (by rw [div_mul_64_add_mod]; exact h_idx_lt))
        | some inner =>
          cases inner with
          | none =>
            refine ⟨none, rfl, ?_⟩
            intro idx h_idx_lo h_idx_lt
            cases Classical.em ((HDiv.hDiv idx.bytes.toNat 64) = startBlock) with
            | inl hk =>
              rw [h_get_eq idx (by rw [hk]; exact h_sb_ib)]
              have h_idx_ge_sb : startBit ≤ HMod.hMod idx.bytes.toNat 64 := by
                have h_le' : startBlock * 64 + startBit ≤ startBlock * 64 + HMod.hMod idx.bytes.toNat 64 := by
                  rw [div_mul_64_add_mod start.bytes.toNat, ← hk, div_mul_64_add_mod idx.bytes.toNat]
                  exact h_idx_lo
                exact Nat.le_of_add_le_add_left h_le'
              have h_p := h_sb0_prop ((HMod.hMod idx.bytes.toNat 64)) h_idx_ge_sb (Nat.mod_lt _ (by decide))
              have _h_simpa := h_p
              simp [hk]
              exact _h_simpa
            | inr hk =>
              have h_in_l : (HDiv.hDiv idx.bytes.toNat 64) ∈ rngList :=
                (h_mem_rng _).mpr ⟨Nat.lt_of_le_of_ne (Nat.div_le_div_right h_idx_lo) (Ne.symm hk),
                  Nat.div_le_div_right (Nat.le_pred_of_lt h_idx_lt)⟩
              rw [h_get_eq idx (h_in_rng _ h_in_l)]
              exact congrArg Except.ok
                (h_loop_prop ((HDiv.hDiv idx.bytes.toNat 64)) h_in_l ((HMod.hMod idx.bytes.toNat 64))
                  (Nat.mod_lt _ (by decide)) (by rw [div_mul_64_add_mod]; exact h_idx_lt))
          | some found =>
            let ⟨blk, h_blk_mem, bit, hbit, h_f_eq, h_f_lt, h_f_tb, h_f_prev⟩ := h_loop_prop
            have h_blk_bounds := (h_mem_rng blk).mp h_blk_mem
            have ⟨h_f_div, h_f_mod⟩ := div_mod_64_of_eq hbit h_f_eq
            have h_s_lt_f : start.bytes.toNat ≤ found.bytes.toNat := by
              rw [← div_mul_64_add_mod start.bytes.toNat, h_f_eq]
              exact mul64_add_le_of_lt_blk (Nat.mod_lt _ (by decide)) h_blk_bounds.1
            refine ⟨some found, rfl, h_s_lt_f, h_f_lt, ?_, ?_⟩
            · rw [h_get_eq found (by rw [h_f_div]; exact h_in_rng blk h_blk_mem)]
              have _h_simpa := h_f_tb
              simp [h_f_div, h_f_mod]
              exact _h_simpa
            · intro idx h_idx_lo h_idx_lt
              cases Classical.em ((HDiv.hDiv idx.bytes.toNat 64) = startBlock) with
              | inl hk =>
                rw [h_get_eq idx (by rw [hk]; exact h_sb_ib)]
                have h_idx_ge_sb : startBit ≤ HMod.hMod idx.bytes.toNat 64 := by
                  have h_le' : startBlock * 64 + startBit ≤ startBlock * 64 + HMod.hMod idx.bytes.toNat 64 := by
                    rw [div_mul_64_add_mod start.bytes.toNat, ← hk, div_mul_64_add_mod idx.bytes.toNat]
                    exact h_idx_lo
                  exact Nat.le_of_add_le_add_left h_le'
                have h_p := h_sb0_prop ((HMod.hMod idx.bytes.toNat 64)) h_idx_ge_sb (Nat.mod_lt _ (by decide))
                have _h_simpa := h_p
                simp [hk]
                exact _h_simpa
              | inr hk =>
                have h_in_l : (HDiv.hDiv idx.bytes.toNat 64) ∈ rngList := (h_mem_rng _).mpr
                  ⟨Nat.lt_of_le_of_ne (Nat.div_le_div_right h_idx_lo) (Ne.symm hk),
                   Nat.le_trans (Nat.div_le_div_right (Nat.le_of_lt h_idx_lt)) (by rw [h_f_div]; exact h_blk_bounds.2)⟩
                rw [h_get_eq idx (h_in_rng _ h_in_l)]
                exact congrArg Except.ok
                  (h_f_prev ((HDiv.hDiv idx.bytes.toNat 64)) h_in_l ((HMod.hMod idx.bytes.toNat 64))
                    (Nat.mod_lt _ (by decide)) (by rw [div_mul_64_add_mod]; exact h_idx_lt))
      | inr h_more =>
        dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [if_neg_eq h_more]
        refine ⟨none, rfl, ?_⟩
        intro idx h_idx_lo h_idx_lt
        have h_idx_div : (HDiv.hDiv idx.bytes.toNat 64) = startBlock := by
          exact Nat.le_antisymm
            (Nat.le_trans (Nat.div_le_div_right (Nat.le_pred_of_lt h_idx_lt)) (Nat.le_of_not_lt h_more))
            (Nat.div_le_div_right h_idx_lo)
        rw [h_get_eq idx (by rw [h_idx_div]; exact h_sb_ib)]
        have h_idx_ge_sb : startBit ≤ HMod.hMod idx.bytes.toNat 64 := by
          have h_le' : startBlock * 64 + startBit ≤ startBlock * 64 + HMod.hMod idx.bytes.toNat 64 := by
            rw [div_mul_64_add_mod start.bytes.toNat, ← h_idx_div, div_mul_64_add_mod idx.bytes.toNat]
            exact h_idx_lo
          exact Nat.le_of_add_le_add_left h_le'
        have h_p := h_sb0_prop ((HMod.hMod idx.bytes.toNat 64)) h_idx_ge_sb
          (Nat.mod_lt _ (by decide))
        have _h_simpa := h_p
        simp [h_idx_div]
        exact _h_simpa

private theorem fromEndpoints_ok_of_le (a b : Size) (h : a.bytes.toNat ≤ b.bytes.toNat) :
    ∃ r, AllocRange.fromEndpoints a b = .ok r ∧ r.start = a ∧
      r.size.bytes.toNat = b.bytes.toNat - a.bytes.toNat := by
  have h_le : a.bytes ≤ b.bytes := UInt64.le_iff_toNat_le.mpr h
  have h_not_lt : ¬(b.bytes < a.bytes) := UInt64.not_lt.mpr h_le
  refine ⟨⟨a, Size.ofBytes (b.bytes - a.bytes)⟩, ?_, rfl, ?_⟩
  · unfold AllocRange.fromEndpoints Size.sub
    simp [h_not_lt, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
  · simp [Size.ofBytes, UInt64.toNat_sub_of_le _ _ h_le]

/-- For a nonempty in-bounds range of a well-formed mask, `isRangeInitialized`
returns `.ok (.ok ())` exactly when every byte of the range is initialized, and
returns some uninitialized sub-range `.ok (.error bad)` whenever a byte of the
range is uninitialized. -/
theorem isRangeInitialized_nonempty_iff (mask : Miri.Memory.InitMask) (range : AllocRange) (finish : Size)
    (valid : Miri.Memory.InitMask.WriteProof.WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    (mask.isRangeInitialized range = .ok (.ok ()) ↔
      ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
        mask.get idx = .ok true) ∧
    ((∃ idx : Size, range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat ∧
        mask.get idx = .ok false) →
      ∃ bad : AllocRange, mask.isRangeInitialized range = .ok (.error bad)) := by
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    have _h_simpa := Nat.not_lt.mpr inBounds
    simp at _h_simpa
    simp [UInt64.lt_iff_toNat_lt]
    exact _h_simpa
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds h_not_oob
    cases blocks with
    | Lazy state =>
      rw [Mirrors.InitMask.isRangeInitialized_eq_R, Mirrors.InitMask.get_eq_getR]
      unfold Mirrors.InitMask.isRangeInitializedR Mirrors.InitMask.getR
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, reduceIte, Pure.pure, Except.pure]
      cases state
      · simp only [Bool.false_eq_true, reduceIte]
        constructor
        · constructor
          · intro h; cases h
          · intro h_all
            have h_start := h_all range.start (Nat.le_refl _) nonempty
            cases h_start
        · intro _
          exact ⟨range, rfl⟩
      · simp only [reduceIte]
        constructor
        · constructor
          · intro _ _ _ _; exact True.intro
          · intro _; exact True.intro
        · intro ⟨_, _, _, hf⟩
          cases hf
    | Materialized mat =>
      dsimp only [Miri.Memory.InitMask.WriteProof.WellFormed] at valid
      have h_cap : finish.bytes.toNat ≤ mat.blocks.size * 64 := Nat.le_trans inBounds valid
      let ⟨uninit?, h_fb0, h_fb0_prop⟩ := findBit_spec mat range.start finish false h_cap
      rw [Mirrors.InitMask.isRangeInitialized_eq_R, Mirrors.InitMask.get_eq_getR]
      unfold Mirrors.InitMask.isRangeInitializedR Mirrors.InitMask.getR
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, reduceIte, h_fb0]
      cases uninit? with
      | none =>
        dsimp only at h_fb0_prop
        dsimp only
        simp only [Bool.not_false] at h_fb0_prop
        simp only [Pure.pure, Except.pure]
        constructor
        · constructor
          · intro _ idx h1 h2; exact h_fb0_prop idx h1 h2
          · intro _; exact True.intro
        · intro ⟨idx, h1, h2, hf⟩
          have ht : Mirrors.InitMaskMaterialized.get mat idx = .ok true := h_fb0_prop idx h1 h2
          rw [ht] at hf
          cases hf
      | some uninitStart =>
        dsimp only at h_fb0_prop
        dsimp only
        let ⟨h_us_lo, h_us_lt, h_us_get, _⟩ := h_fb0_prop
        let ⟨end?, h_fb1, h_fb1_prop⟩ := findBit_spec mat uninitStart finish true h_cap
        rw [h_fb1]
        simp only [Pure.pure, Except.pure]
        have h_end_ge : uninitStart.bytes.toNat ≤ (end?.getD finish).bytes.toNat := by
          cases end? with
          | none => exact Nat.le_of_lt h_us_lt
          | some e => exact h_fb1_prop.1
        let ⟨bad, h_bad, _, _⟩ := fromEndpoints_ok_of_le uninitStart (end?.getD finish) h_end_ge
        rw [h_bad]
        dsimp only
        constructor
        · constructor
          · intro h; cases h
          · intro h_all
            have ht := h_all uninitStart h_us_lo h_us_lt
            rw [h_us_get] at ht
            cases ht
        · intro _
          exact ⟨bad, rfl⟩

/-- Marking a nonempty in-bounds range initialized makes `isRangeInitialized`
succeed on that range. -/
theorem isRangeInitialized_after_setRange_true (mask updated : Miri.Memory.InitMask)
    (range : AllocRange) (finish : Size)
    (valid : Miri.Memory.InitMask.WriteProof.WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (h_set : mask.setRange range true = .ok updated) :
    updated.isRangeInitialized range = .ok (.ok ()) := by
  let ⟨u, h_u, h_len, h_wf⟩ := Miri.Memory.InitMask.WriteProof.set_range_exists mask range finish true valid endpoint nonempty inBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u range finish h_wf endpoint nonempty (by rw [h_len]; exact inBounds)).1]
  intro idx h_lo h_hi
  have h_idx_ib : idx.bytes.toNat < mask.len.bytes.toNat := Nat.lt_of_lt_of_le h_hi inBounds
  rw [set_range_get mask u range finish idx true valid endpoint nonempty inBounds h_idx_ib h_u]
  rw [if_pos_eq ⟨h_lo, h_hi⟩]

/--
Frame rule: a `setRange` on one nonempty in-bounds range does not change whether
a disjoint nonempty in-bounds range is fully initialized.
-/
theorem isRangeInitialized_frame (mask updated : Miri.Memory.InitMask)
    (writeRange queryRange : AllocRange) (writeFinish queryFinish : Size) (state : Bool)
    (valid : Miri.Memory.InitMask.WriteProof.WellFormed mask)
    (wEnd : writeRange.endExclusive = .ok writeFinish)
    (qEnd : queryRange.endExclusive = .ok queryFinish)
    (wNonempty : writeRange.start.bytes.toNat < writeFinish.bytes.toNat)
    (qNonempty : queryRange.start.bytes.toNat < queryFinish.bytes.toNat)
    (wInBounds : writeFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (qInBounds : queryFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (disjoint : writeFinish.bytes.toNat ≤ queryRange.start.bytes.toNat ∨
      queryFinish.bytes.toNat ≤ writeRange.start.bytes.toNat)
    (h_set : mask.setRange writeRange state = .ok updated) :
    (updated.isRangeInitialized queryRange = .ok (.ok ()) ↔
      mask.isRangeInitialized queryRange = .ok (.ok ())) := by
  let ⟨u, h_u, h_len, h_wf⟩ := Miri.Memory.InitMask.WriteProof.set_range_exists mask writeRange writeFinish state valid wEnd wNonempty wInBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u queryRange queryFinish h_wf qEnd qNonempty (by rw [h_len]; exact qInBounds)).1]
  rw [(isRangeInitialized_nonempty_iff mask queryRange queryFinish valid qEnd qNonempty qInBounds).1]
  constructor
  · intro h idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := fun ⟨hw1, hw2⟩ =>
      Or.elim disjoint (fun hd => Nat.not_lt.mpr (Nat.le_trans hd h_lo) hw2)
        (fun hd => Nat.not_le_of_lt (Nat.lt_of_lt_of_le h_hi hd) hw1)
    have h_idx_ib : idx.bytes.toNat < mask.len.bytes.toNat := Nat.lt_of_lt_of_le h_hi qInBounds
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds h_idx_ib h_u
    rw [if_neg_eq h_out] at h_get
    exact h_get.symm.trans (h idx h_lo h_hi)
  · intro h idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := fun ⟨hw1, hw2⟩ =>
      Or.elim disjoint (fun hd => Nat.not_lt.mpr (Nat.le_trans hd h_lo) hw2)
        (fun hd => Nat.not_le_of_lt (Nat.lt_of_lt_of_le h_hi hd) hw1)
    have h_idx_ib : idx.bytes.toNat < mask.len.bytes.toNat := Nat.lt_of_lt_of_le h_hi qInBounds
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds h_idx_ib h_u
    rw [if_neg_eq h_out] at h_get
    exact h_get.trans (h idx h_lo h_hi)

-- Excluded under Option C (#4009): `InitMask.WriteProof.prepareCopy_of_uniform`
-- requires unfolding `_private...Miri.Memory.InitMask.collectChunksAux`
-- (implicitly `@[irreducible]` and `private` in unmodified `InitMask.lean`).
-- Deferred to follow-up.


/--
Applying a single-run copy encoding `⟨state, #[srcSize.bytes]⟩` (with `srcSize`
nonzero) `repeatCount` times starting at `destStart` is `setRange` of the whole
span `allocRange destStart total` to `state`, where
`Size.mul srcSize repeatCount = .ok total`.
-/
theorem applyCopy_singleton (destMask : Miri.Memory.InitMask) (destStart srcSize total : Size)
    (repeatCount : UInt64) (state : Bool)
    (nonzero : srcSize.bytes ≠ 0)
    (h_mul : Size.mul srcSize repeatCount = .ok total) :
    destMask.applyCopy ⟨state, [srcSize.bytes].toArray⟩ (allocRange destStart srcSize) repeatCount =
      destMask.setRange (allocRange destStart total) state := by
  unfold Miri.Memory.InitMask.applyCopy
  simp [nonzero, allocRange, h_mul, Except.mapError, Bind.bind, Except.bind]

end InitMask.WriteProof
/-! ## Part 2. `ProvenanceMap` -/

/-!
### 2a. Private mirrors of private `ProvenanceMap` helpers and `rfl` bridges
-/

namespace Mirrors.ProvenanceMap
open Miri.ABI
open Miri.Memory

private def rangeEntries {α : Type} (values : Array (Size × α)) (start finish : Size) :
    Array (Size × α) :=
  values.filter fun entry => start.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes

private def adjustedStart (range : AllocRange) (pointerSize : Size) :
    Except ProvenanceMapError Size :=
  if pointerSize.bytes == 0 then .error .pointerSizeZero
  else .ok (Size.ofBytes (UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat - 1))))

private def rangeEnd (range : AllocRange) : Except ProvenanceMapError Size :=
  range.endExclusive.mapError .memory

private def subtractSize (left right : Size) : Except ProvenanceMapError Size :=
  (Size.sub left right).mapError (fun e => ProvenanceMapError.memory (MemoryError.sizeError e))

private def ptrFragments {Prov : Type} (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (pointerSize : Size) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) :=
  have kMain := fun (_r : Unit) =>
    Bind.bind
      (Except.mapError (fun e => ProvenanceMapError.memory (MemoryError.sizeError e)) (position.add pointerSize))
      fun _finish =>
        if h : position.bytes.toNat + pointerSize.bytes.toNat ≤ data.size then
          have bytes : Vector UInt8 8 := Vector.ofFn fun index =>
            if hi : index.val < pointerSize.bytes.toNat then
              GetElem.getElem data (position.bytes.toNat + index.val)
                (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) h)
            else 0
          have fragments : Array (Size × PointerFrag Prov) := List.nil.toArray
          Bind.bind
            (forIn ({ stop := pointerSize.bytes.toNat,
                      step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
              fragments
              fun index s =>
                have fragments := s
                have pos := Size.ofBytes (position.bytes + UInt64.ofNat index)
                if inRange pos = true then
                  have fragments := fragments.push (pos, ⟨UInt8.ofNat index, prov, bytes⟩)
                  Pure.pure (ForInStep.yield fragments)
                else Pure.pure (ForInStep.yield fragments))
            fun s =>
              have fragments := s
              Pure.pure fragments
        else throw (.fragmentSliceOutOfBounds position pointerSize data.size)
  if pointerSize.bytes > 8 then
    Bind.bind (throw (.pointerSizeExceedsFragmentStorage pointerSize.bytes)) fun r => kMain r
  else kMain Unit.unit

private def rangePtrsR {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : AllocRange) (pointerSize : Size) :
    Except ProvenanceMapError (Array (Size × Prov)) :=
  Bind.bind (adjustedStart range pointerSize) fun start =>
    Bind.bind (rangeEnd range) fun finish =>
      Pure.pure (rangeEntries self.ptrs start finish)

private def rangeBytesR {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : AllocRange) : Except ProvenanceMapError (Array (Size × PointerFrag Prov)) :=
  Bind.bind (rangeEnd range) fun finish =>
    Pure.pure (rangeEntries (self.byteFragments.getD List.nil.toArray) range.start finish)

private def prepareCopyR {Prov : Type} (self : Miri.Memory.ProvenanceMap Prov)
    (range : AllocRange) (data : Array UInt8) (pointerSize : Size) :
    Except ProvenanceMapError (ProvenanceCopy Prov) :=
  have kNZ : Unit → Except ProvenanceMapError (ProvenanceCopy Prov) := fun (_r : Unit) =>
    Bind.bind (rangeEnd range) fun finish =>
      have ptrs : Array (Size × Prov) := List.nil.toArray
      have kPtrs : Unit → Array (Size × Prov) → Except ProvenanceMapError (ProvenanceCopy Prov) :=
        fun (_r : Unit) (ptrs : Array (Size × Prov)) =>
        Bind.bind (self.rangePtrs (allocRange range.start Size.ZERO) pointerSize) fun rps =>
          have beginOverlap : Option (Size × Prov) := rps[0]?
          Bind.bind (self.rangePtrs (allocRange finish Size.ZERO) pointerSize) fun rpf =>
            have endOverlap : Option (Size × Prov) := rpf[0]?
            have bytes : Array (Size × PointerFrag Prov) := List.nil.toArray
            have kRet : Unit → Array (Size × PointerFrag Prov) → Except ProvenanceMapError (ProvenanceCopy Prov) :=
              fun (_r : Unit) (bytes : Array (Size × PointerFrag Prov)) =>
                Pure.pure { ptrs := ptrs, byteFragments := bytes }
            if ((beginOverlap.isSome || endOverlap.isSome) || self.byteFragments.isSome) = true then
              have kAfterBegin :
                  Unit → Array (Size × PointerFrag Prov) → Except ProvenanceMapError (ProvenanceCopy Prov) :=
                fun (_r : Unit) (bytes : Array (Size × PointerFrag Prov)) =>
                Bind.bind (self.rangeBytes range) fun rbs =>
                  Bind.bind
                    (forIn rbs bytes fun x s =>
                      have bytes : Array (Size × PointerFrag Prov) := s
                      match x with
                      | (offset, frag) =>
                        Bind.bind (subtractSize offset range.start) fun sft =>
                          have bytes : Array (Size × PointerFrag Prov) := bytes.push (sft, frag)
                          Pure.pure (ForInStep.yield bytes))
                    fun s =>
                      have bytes : Array (Size × PointerFrag Prov) := s
                      match endOverlap with
                      | some (position, prov) =>
                        if ((Option.map (fun x => match x with | (b, _) => b.bytes != position.bytes)
                              beginOverlap).getD true) = true then
                          have kEndFrags : Unit → Except ProvenanceMapError (ProvenanceCopy Prov) :=
                            fun (_r : Unit) =>
                            if position.bytes < finish.bytes then
                              Bind.bind
                                (ptrFragments
                                  (fun pos => (decide (position.bytes ≤ pos.bytes)) &&
                                    (decide (pos.bytes < finish.bytes)))
                                  position prov data pointerSize)
                                fun fragments =>
                                  Bind.bind
                                    (forIn fragments bytes fun x s =>
                                      have bytes : Array (Size × PointerFrag Prov) := s
                                      match x with
                                      | (pos, frag) =>
                                        Bind.bind (subtractSize pos range.start) fun shifted =>
                                          have kPush :
                                              Unit → Except ProvenanceMapError
                                                (ForInStep (Array (Size × PointerFrag Prov))) :=
                                            fun (_r : Unit) =>
                                            have bytes : Array (Size × PointerFrag Prov) :=
                                              bytes.push (shifted, frag)
                                            Pure.pure (ForInStep.yield bytes)
                                          if (!((Option.map (fun last =>
                                                  decide (last.1.bytes < shifted.bytes))
                                                  bytes.back?).getD true)) = true then
                                            Bind.bind (throw .unsortedOrDuplicateKeys) fun r =>
                                              kPush r
                                          else kPush Unit.unit)
                                    fun s =>
                                      have bytes : Array (Size × PointerFrag Prov) := s
                                      kRet Unit.unit bytes
                            else kRet Unit.unit bytes
                          if position.bytes < range.start.bytes then
                            Bind.bind (throw .unsortedOrDuplicateKeys) fun r => kEndFrags r
                          else kEndFrags Unit.unit
                        else kRet Unit.unit bytes
                      | _ => kRet Unit.unit bytes
              match beginOverlap with
              | some (position, prov) =>
                Bind.bind
                  (Except.mapError (fun e => ProvenanceMapError.memory (MemoryError.sizeError e))
                    (position.add pointerSize))
                  fun ptrEnd =>
                    have fragmentEnd : Size := if ptrEnd.bytes < finish.bytes then ptrEnd else finish
                    if range.start.bytes < fragmentEnd.bytes then
                      Bind.bind
                        (ptrFragments
                          (fun pos => (decide (range.start.bytes ≤ pos.bytes)) &&
                            (decide (pos.bytes < fragmentEnd.bytes)))
                          position prov data pointerSize)
                        fun fragments =>
                          Bind.bind
                            (forIn fragments bytes fun x s =>
                              have bytes : Array (Size × PointerFrag Prov) := s
                              match x with
                              | (pos, frag) =>
                                Bind.bind (subtractSize pos range.start) fun sft =>
                                  have bytes : Array (Size × PointerFrag Prov) := bytes.push (sft, frag)
                                  Pure.pure (ForInStep.yield bytes))
                            fun s =>
                              have bytes : Array (Size × PointerFrag Prov) := s
                              kAfterBegin Unit.unit bytes
                    else kAfterBegin Unit.unit bytes
              | _ => kAfterBegin Unit.unit bytes
            else kRet Unit.unit bytes
      if range.size.bytes ≥ pointerSize.bytes then
        Bind.bind (subtractSize finish (Size.ofBytes (pointerSize.bytes - 1))) fun adjustedEnd =>
          Bind.bind
            (forIn (rangeEntries self.ptrs range.start adjustedEnd) ptrs fun x s =>
              have ptrs : Array (Size × Prov) := s
              match x with
              | (offset, prov) =>
                Bind.bind (subtractSize offset range.start) fun sft =>
                  have ptrs : Array (Size × Prov) := ptrs.push (sft, prov)
                  Pure.pure (ForInStep.yield ptrs))
            fun s =>
              have ptrs : Array (Size × Prov) := s
              kPtrs Unit.unit ptrs
      else kPtrs Unit.unit ptrs
  if pointerSize.bytes == 0 then
    Bind.bind (throw .pointerSizeZero) fun r => kNZ r
  else kNZ Unit.unit

private theorem rangePtrs_eq_R {Prov : Type} :
    @Miri.Memory.ProvenanceMap.rangePtrs Prov = @rangePtrsR Prov := rfl
private theorem rangeBytes_eq_R {Prov : Type} :
    @Miri.Memory.ProvenanceMap.rangeBytes Prov = @rangeBytesR Prov := rfl
private theorem prepareCopy_eq_R {Prov : Type} :
    @Miri.Memory.ProvenanceMap.prepareCopy Prov = @prepareCopyR Prov := rfl

end Mirrors.ProvenanceMap

/-! ### 2b. The four `Miri.Memory.ProvenanceMap` specification theorems -/

namespace ProvenanceMap
open Miri.ABI Miri.Memory
variable {P : Type}

private theorem empty_range (range : AllocRange) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0) (endEq : range.endExclusive = .ok finish) :
    (Miri.Memory.ProvenanceMap.new (Prov := P)).rangeEmpty range pointerSize = .ok true := by
  unfold Miri.Memory.ProvenanceMap.rangeEmpty
  rw [Mirrors.ProvenanceMap.rangePtrs_eq_R, Mirrors.ProvenanceMap.rangeBytes_eq_R]
  unfold Mirrors.ProvenanceMap.rangePtrsR Mirrors.ProvenanceMap.rangeBytesR Mirrors.ProvenanceMap.adjustedStart Mirrors.ProvenanceMap.rangeEnd Mirrors.ProvenanceMap.rangeEntries
  simp [Miri.Memory.ProvenanceMap.new, positive, endEq, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

/--
The empty provenance map has no provenance in any non-overflowing range (for a
nonzero pointer size).
-/
theorem rangeEmpty_new (range : AllocRange) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0) (endEq : range.endExclusive = .ok finish) :
    (Miri.Memory.ProvenanceMap.new (Prov := P)).rangeEmpty range pointerSize = .ok true :=
  empty_range range pointerSize finish positive endEq

/-- Reading a pointer from the empty provenance map yields no provenance (for a
nonzero pointer size and a non-overflowing pointer range). -/
theorem readPtr_new [DecidableEq P] [PointerProvenance P]
    (offset pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0)
    (endEq : (allocRange offset pointerSize).endExclusive = .ok finish) :
    (Miri.Memory.ProvenanceMap.new (Prov := P)).readPtr offset pointerSize = .ok none := by
  unfold Miri.Memory.ProvenanceMap.readPtr Miri.Memory.ProvenanceMap.getPtr
  rw [Mirrors.ProvenanceMap.rangePtrs_eq_R, Mirrors.ProvenanceMap.rangeBytes_eq_R]
  unfold Mirrors.ProvenanceMap.rangePtrsR Mirrors.ProvenanceMap.rangeBytesR Mirrors.ProvenanceMap.adjustedStart Mirrors.ProvenanceMap.rangeEnd Mirrors.ProvenanceMap.rangeEntries Miri.Memory.ProvenanceMap.new
  simp [positive, endEq, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

/--
Preparing a provenance copy from the empty provenance map yields the empty copy
(for a nonzero pointer size and a non-overflowing range).
-/
theorem prepareCopy_new (range : AllocRange) (data : Array UInt8) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0)
    (endEq : range.endExclusive = .ok finish) :
    (Miri.Memory.ProvenanceMap.new (Prov := P)).prepareCopy range data pointerSize = .ok ⟨List.nil.toArray, List.nil.toArray⟩ := by
  have h_start0 : (allocRange range.start Size.ZERO).endExclusive = .ok range.start := by
    cases range.start
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_fin0 : (allocRange finish Size.ZERO).endExclusive = .ok finish := by
    cases finish
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_rp_start : (Miri.Memory.ProvenanceMap.new (Prov := P)).rangePtrs (allocRange range.start Size.ZERO) pointerSize = .ok List.nil.toArray := by
    rw [Mirrors.ProvenanceMap.rangePtrs_eq_R]
    unfold Mirrors.ProvenanceMap.rangePtrsR Mirrors.ProvenanceMap.adjustedStart Mirrors.ProvenanceMap.rangeEnd Mirrors.ProvenanceMap.rangeEntries Miri.Memory.ProvenanceMap.new
    simp [positive, h_start0, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]
  have h_rp_fin : (Miri.Memory.ProvenanceMap.new (Prov := P)).rangePtrs (allocRange finish Size.ZERO) pointerSize = .ok List.nil.toArray := by
    rw [Mirrors.ProvenanceMap.rangePtrs_eq_R]
    unfold Mirrors.ProvenanceMap.rangePtrsR Mirrors.ProvenanceMap.adjustedStart Mirrors.ProvenanceMap.rangeEnd Mirrors.ProvenanceMap.rangeEntries Miri.Memory.ProvenanceMap.new
    simp [positive, h_fin0, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]
  rw [Mirrors.ProvenanceMap.prepareCopy_eq_R]
  unfold Mirrors.ProvenanceMap.prepareCopyR
  simp only [positive, beq_iff_eq, reduceIte, Mirrors.ProvenanceMap.rangeEnd, endEq, Except.mapError,
    h_rp_start, h_rp_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases Classical.em (pointerSize.bytes ≤ range.size.bytes) with
  | inl h_ge =>
    have h_le_fin : pointerSize.bytes - 1 ≤ finish.bytes := by
      have h_end_def : Size.add range.start range.size = .ok finish := by
        unfold AllocRange.endExclusive AllocRange.end at endEq
        cases h_add : Size.add range.start range.size with
        | error e => simp [h_add, Except.mapError] at endEq
        | ok f => have _h := endEq; simp [h_add, Except.mapError] at _h; simp; exact _h
      unfold Size.add at h_end_def
      cases Classical.em (range.start.bytes + range.size.bytes < range.start.bytes) with
      | inl h_wrap =>
        simp [h_wrap] at h_end_def
      | inr h_wrap =>
        simp only [h_wrap, reduceIte, Except.ok.injEq] at h_end_def
        subst h_end_def
        have h_ge_nat : pointerSize.bytes.toNat ≤ range.size.bytes.toNat := UInt64.le_iff_toNat_le.mp h_ge
        have h_nw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
          have _h_simpa := h_wrap
          simp [UInt64.lt_iff_toNat_lt] at _h_simpa
          simp
          exact _h_simpa
        have h1 := range.start.bytes.toNat_lt
        have h2 := range.size.bytes.toNat_lt
        have h_nw' : ¬(HMod.hMod (range.start.bytes.toNat + range.size.bytes.toNat) (HPow.hPow (2 : Nat) 64) < range.start.bytes.toNat) := by
          rw [← UInt64.toNat_add]; exact h_nw
        have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < (HPow.hPow (2 : Nat) 64) :=
          add_lt_two_pow_64_of_not_wrap h1 h2 h_nw'
        have h_p1 : pointerSize.bytes.toNat ≠ 0 := fun h0 => positive (UInt64.toNat_inj.mp h0)
        have h_sub : (pointerSize.bytes - 1).toNat = pointerSize.bytes.toNat - 1 := by
          have h_u1 : (1 : UInt64).toNat = 1 := rfl
          rw [UInt64.toNat_sub_of_le]
          · exact congrArg (pointerSize.bytes.toNat - ·) h_u1
          · exact UInt64.le_iff_toNat_le.mpr (by rw [h_u1]; exact Nat.pos_of_ne_zero h_p1)
        simp only [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
        rw [h_sub]
        exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans h_ge_nat (Nat.le_add_left _ _))
    have h_not_lt : ¬(finish.bytes < pointerSize.bytes - 1) := UInt64.not_lt.mpr h_le_fin
    have h_sub_ok : Mirrors.ProvenanceMap.subtractSize finish (Size.ofBytes (pointerSize.bytes - 1)) =
        .ok (Size.ofBytes (finish.bytes - (pointerSize.bytes - 1))) := by
      unfold Mirrors.ProvenanceMap.subtractSize Size.sub Size.ofBytes
      simp [h_not_lt, Except.mapError]
    simp only [ge_iff_le, h_ge, reduceIte, h_sub_ok]
    have h_re : Mirrors.ProvenanceMap.rangeEntries (Miri.Memory.ProvenanceMap.new (Prov := P)).ptrs range.start
        (Size.ofBytes (finish.bytes - (pointerSize.bytes - 1))) = List.nil.toArray := rfl
    rw [h_re]
    rfl
  | inr h_ge =>
    simp only [ge_iff_le, h_ge, reduceIte]
    rfl

/-- Applying the empty provenance copy leaves any provenance map unchanged. -/
theorem applyCopy_empty (range : AllocRange) (repeatCount : UInt64) (pm : Miri.Memory.ProvenanceMap P) :
    Miri.Memory.ProvenanceMap.applyCopy ⟨List.nil.toArray, List.nil.toArray⟩ range repeatCount pm = .ok () pm := by
  unfold Miri.Memory.ProvenanceMap.applyCopy
  simp [pure, Pure.pure, EStateM.pure]

end ProvenanceMap
/-! ## Part 3. `Allocation` -/

/-! ### 3a. Private mirrors of private `Allocation` helpers -/

namespace Mirrors
open Miri.ABI
open Miri.Memory

private def maxU64Nat : Nat := 18446744073709551615

private def checkedAlign (align : Align) : Except AllocError Align :=
  Bind.bind ((Align.bytes align).mapError AllocError.alignment) fun bytes =>
    Bind.bind ((Align.fromBytes bytes).mapError AllocError.alignment) fun normalized =>
      if normalized == align then Pure.pure align
      else throw (.alignment (.tooLarge bytes))

private def sizeForArray (length : Nat) : Except AllocError Size :=
  if length > maxU64Nat then throw (.storageLengthOverflow length)
  else
    let size := Size.ofBytes (UInt64.ofNat length)
    if size.bytes.toNat == length then Pure.pure size
    else throw (.storageLengthOverflow length)

private def pointerSize (layout : TargetDataLayout) : Size :=
  Size.fromBits layout.pointerWidth.bits

private def targetUIntBytes (layout : TargetDataLayout) (size : Size) (bits : U128) :
    Except AllocError (Array UInt8) :=
  have kMain := fun (_r : Unit) =>
    have count := size.bytes.toNat
    have result : Array UInt8 := List.nil.toArray
    Bind.bind
      (forIn ({ stop := count, step_pos := Nat.zero_lt_one } : Std.Legacy.Range) result
        fun index s =>
          have result := s
          have valueIndex :=
            if layout.endian == .little then index else count - index - 1
          have byte :=
            HMod.hMod (HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 * valueIndex))) 256
          have result := result.push (UInt8.ofNat byte)
          Pure.pure (ForInStep.yield result))
      fun s =>
        have result := s
        Pure.pure result
  if size.bytes > 16 then
    Bind.bind (throw (.scalarBytesTooWide size)) fun r => kMain r
  else kMain Unit.unit

private def readTargetUInt (layout : TargetDataLayout) (bytes : Array UInt8) :
    Except AllocError U128 :=
  have kMain := fun (_r : Unit) =>
    have value := (0 : Nat)
    Bind.bind
      (forIn ({ stop := bytes.size, step_pos := Nat.zero_lt_one } : Std.Legacy.Range) value
        fun index s =>
          have value := s
          match bytes[index]? with
          | some byte =>
            have valueIndex :=
              if layout.endian == .little then index else bytes.size - index - 1
            have value := value + byte.toNat * HPow.hPow (2 : Nat) (8 * valueIndex)
            Pure.pure (ForInStep.yield value)
          | _ =>
            Bind.bind (throw (α := Unit) (.invalidSliceEndpoints index (index + 1) bytes.size))
              fun (_r : Unit) => Pure.pure (ForInStep.yield value))
      fun s =>
        have value := s
        Pure.pure (BitVec.ofNat 128 value)
  if bytes.size > 16 then
    Bind.bind (throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))) fun r => kMain r
  else kMain Unit.unit

private def firstNonZero (bytes : Array UInt8) : Option (Nat × UInt8) :=
  Id.run
    (Bind.bind
      (forIn (m := Id) ({ stop := bytes.size, step_pos := Nat.zero_lt_one } : Std.Legacy.Range)
        ((none : Option (Option (Nat × UInt8))), Unit.unit)
        fun index _ =>
          match bytes[index]? with
          | some byte =>
            if (byte != 0) = true then
              Pure.pure (ForInStep.done (some (some (index, byte)), Unit.unit))
            else Pure.pure (ForInStep.yield (none, Unit.unit))
          | none => Pure.pure (ForInStep.done (some (some (index, (0 : UInt8))), Unit.unit)))
      fun s =>
        have r := s
        Break.runK.match_1 (fun _ => Id (Option (Nat × UInt8))) r.1
          (fun r => Pure.pure r) fun _ => Pure.pure none)

namespace Allocation

variable {Prov Extra : Type}

/-- The private `Allocation.mk`, built with the standard `constructor` tactic.
-/
private def mkAlloc (rawBytes : Array UInt8) (size : Size)
    (provenance : Miri.Memory.ProvenanceMap Prov)
    (initMask : Miri.Memory.InitMask) (align : Align) (mutability : Mutability)
    (extra : Extra) (nativeBuffer : Option NativeBufferOwnership) :
    Miri.Memory.Allocation Prov Extra := by
  constructor
  · exact rawBytes
  · exact size
  · exact provenance
  · exact initMask
  · exact align
  · exact mutability
  · exact extra
  · exact nativeBuffer

/-- The private `rawBytes` field, read through the public `casesOn` eliminator.
-/
private def raw (allocation : Miri.Memory.Allocation Prov Extra) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) allocation
    (fun rawBytes _ _ _ _ _ _ _ => rawBytes)

private def checkedSlice (allocation : Miri.Memory.Allocation Prov Extra)
    (range : AllocRange) : Except AllocError (Array UInt8) :=
  if (raw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (raw allocation).size)
  else
    Bind.bind ((range.endExclusive).mapError AllocError.memory) fun finish =>
      if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
        throw (.outOfBounds range allocation.byteSize)
      else Pure.pure ((raw allocation).extract range.start.bytes.toNat finish.bytes.toNat)

private def withProvenance (state : Miri.Memory.Allocation Prov Extra)
    (provenance : Miri.Memory.ProvenanceMap Prov) : Miri.Memory.Allocation Prov Extra :=
  mkAlloc (raw state) state.byteSize provenance state.initializationMask state.align
    state.mutability state.extra state.nativeBuffer

private def withInitMask (state : Miri.Memory.Allocation Prov Extra)
    (initMask : Miri.Memory.InitMask) : Miri.Memory.Allocation Prov Extra :=
  mkAlloc (raw state) state.byteSize state.provenanceMap initMask state.align
    state.mutability state.extra state.nativeBuffer

private def withRawBytes (state : Miri.Memory.Allocation Prov Extra)
    (rawBytes : Array UInt8) : Miri.Memory.Allocation Prov Extra :=
  mkAlloc rawBytes state.byteSize state.provenanceMap state.initializationMask state.align
    state.mutability state.extra state.nativeBuffer


private def setInitialization (state : Miri.Memory.Allocation Prov Extra)
    (range : AllocRange) (initialized : Bool) :
    Except AllocError (Miri.Memory.Allocation Prov Extra) :=
  Bind.bind
    ((state.initializationMask.setRange range initialized).mapError AllocError.memory)
    fun initMask => Pure.pure (withInitMask state initMask)

private def overwriteRawBytes (state : Miri.Memory.Allocation Prov Extra)
    (range : AllocRange) (bytes : Array UInt8) :
    Except AllocError (Miri.Memory.Allocation Prov Extra) :=
  Bind.bind ((range.endExclusive).mapError AllocError.memory) fun finish =>
    let start := range.start.bytes.toNat
    let endIndex := finish.bytes.toNat
    let updated := (raw state).extract 0 start ++ bytes ++
      (raw state).extract endIndex (raw state).size
    if updated.size != state.byteSize.bytes.toNat then
      throw (.storageLengthMismatch state.byteSize updated.size)
    else Pure.pure (withRawBytes state updated)


private def writeBytesR (start : Size) (bytes : Array UInt8) (pointerSize : Size) :
    EStateM AllocError (Miri.Memory.Allocation Prov Extra) Unit :=
  fun state =>
    Id.run
      (match sizeForArray bytes.size with
       | .ok size =>
         Bind.bind (Pure.pure size) fun writeSize =>
           have range := allocRange start writeSize
           match checkedSlice state range with
           | .error reason => Pure.pure (.error reason state)
           | .ok _ =>
             if writeSize.bytes == 0 then Pure.pure (.ok Unit.unit state)
             else if (state.mutability != .Mut) = true then Pure.pure (.error .readOnlyAllocation state)
             else
               match setInitialization state range true with
               | .ok initialized =>
                 Bind.bind (Pure.pure initialized) fun initialized =>
                   have clearedResult := initialized.provenanceMap.clear range (raw initialized) pointerSize
                   match clearedResult with
                   | .ok () provenance =>
                     Bind.bind (Pure.pure (withProvenance initialized provenance)) fun cleared =>
                       match overwriteRawBytes cleared range bytes with
                       | .ok updated => Pure.pure (.ok Unit.unit updated)
                       | .error reason => Pure.pure (.error reason cleared)
                   | .error reason provenance =>
                     Pure.pure (.error (.provenance reason) (withProvenance initialized provenance))
               | .error reason => Pure.pure (.error reason state)
       | .error reason => Pure.pure (.error reason state))

private def writeUninitR (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Miri.Memory.Allocation Prov Extra) Unit :=
  fun state =>
    Id.run
      (match checkedSlice state range with
       | .error reason => Pure.pure (.error reason state)
       | .ok _ =>
         if range.size.bytes == 0 then Pure.pure (.ok Unit.unit state)
         else if (state.mutability != .Mut) = true then Pure.pure (.error .readOnlyAllocation state)
         else
           match setInitialization state range false with
           | .ok uninitialized =>
             Bind.bind (Pure.pure uninitialized) fun uninitialized =>
               have cleared := uninitialized.provenanceMap.clear range (raw uninitialized) pointerSize
               match cleared with
               | .ok () provenance => Pure.pure (.ok Unit.unit (withProvenance uninitialized provenance))
               | .error reason provenance =>
                 Pure.pure (.error (.provenance reason) (withProvenance uninitialized provenance))
           | .error reason => Pure.pure (.error reason state))

private def clearProvenanceR (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Miri.Memory.Allocation Prov Extra) Unit :=
  fun state =>
    match checkedSlice state range with
    | .error reason => .error reason state
    | .ok _ =>
      match state.provenanceMap.clear range (raw state) pointerSize with
      | .ok () provenance => .ok () (withProvenance state provenance)
      | .error reason provenance =>
        .error (.provenance reason) (withProvenance state provenance)

private def fromBytesR (bytes : Array UInt8) (align : Align) (mutability : Mutability) :
    Except AllocError (Miri.Memory.Allocation Prov Unit) :=
  Bind.bind (checkedAlign align) fun align =>
    Bind.bind (sizeForArray bytes.size) fun size =>
      if _h : bytes.size = size.bytes.toNat then
        Pure.pure (mkAlloc bytes size ProvenanceMap.new (InitMask.new size true)
          align mutability () none)
      else
        throw (.storageLengthOverflow bytes.size)

private def tryNewR (size : Size) (align : Align) (init : AllocInit)
    (zeroedStorage : Size → Align → Option (Array UInt8)) :
    Except AllocError (Miri.Memory.Allocation Prov Unit) :=
  Bind.bind (checkedAlign align) fun align =>
    have kBytes : Array UInt8 → Except AllocError (Miri.Memory.Allocation Prov Unit) := fun bytes =>
      have kSize : Unit → Except AllocError (Miri.Memory.Allocation Prov Unit) := fun _r =>
        have kZero : Unit → Except AllocError (Miri.Memory.Allocation Prov Unit) := fun _r =>
          have initialized := match init with | .Uninit => false | .Zero => true
          if _h : bytes.size = size.bytes.toNat then
            Pure.pure (mkAlloc bytes size ProvenanceMap.new (InitMask.new size initialized)
              align .Mut () none)
          else throw (.storageLengthMismatch size bytes.size)
        match firstNonZero bytes with
        | some (index, value) =>
          Bind.bind (throw (.storageBackendNotZeroed index value)) fun r => kZero r
        | _ => kZero Unit.unit
      if (bytes.size != size.bytes.toNat) = true then
        Bind.bind (throw (.storageLengthMismatch size bytes.size)) fun r => kSize r
      else kSize Unit.unit
    match zeroedStorage size align with
    | some bytes => Bind.bind (Pure.pure bytes) fun b => kBytes b
    | none => Bind.bind (throw .hostMemoryExhausted) fun b => kBytes b

private def getBytesStripProvenanceR [PointerProvenance Prov]
    (allocation : Miri.Memory.Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) : Except AllocError (Array UInt8) :=
  Bind.bind
    (Except.mapError AllocError.memory (allocation.initializationMask.isRangeInitialized range))
    fun res =>
      have kSlice : Unit → Except AllocError (Array UInt8) := fun _r =>
        checkedSlice allocation range
      have kCheck : Unit → Except AllocError (Array UInt8) := fun _r =>
        if (!PointerProvenance.offsetIsAddr (Prov := Prov)) = true then
          have ptrBytes := pointerSize layout
          Bind.bind
            (Except.mapError AllocError.provenance (allocation.provenanceMap.rangeEmpty range ptrBytes))
            fun isEmpty =>
              if (!isEmpty) = true then
                Bind.bind
                  (Except.mapError AllocError.provenance (allocation.provenanceMap.getRange range ptrBytes))
                  fun entries =>
                    match entries[0]? with
                    | some (provRange, _) =>
                      Bind.bind (Except.mapError AllocError.memory provRange.endExclusive) fun provFinish =>
                        Bind.bind (Except.mapError AllocError.memory range.endExclusive) fun rangeFinish =>
                          have badStart : Size :=
                            if provRange.start.bytes > range.start.bytes then provRange.start else range.start
                          have badFinish : Size :=
                            if provFinish.bytes < rangeFinish.bytes then provFinish else rangeFinish
                          Bind.bind
                            (Except.mapError AllocError.memory (AllocRange.fromEndpoints badStart badFinish))
                            fun bad =>
                              Bind.bind (throw (.readPointerAsInt (some ⟨range, bad⟩))) fun r => kSlice r
                    | _ =>
                      Bind.bind (throw .nonEmptyProvenanceWithoutEntry) fun r => kSlice r
              else kSlice Unit.unit
        else kSlice Unit.unit
      match res with
      | .error bad => Bind.bind (throw (.invalidUninitBytes (some ⟨range, bad⟩))) kCheck
      | .ok () => kCheck Unit.unit

private def readScalarR [DecidableEq Prov] [PointerProvenance Prov]
    (allocation : Miri.Memory.Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    Except AllocError (Scalar Prov) :=
  Bind.bind
    (Except.mapError AllocError.memory (allocation.initializationMask.isRangeInitialized range))
    fun res =>
      have kMain : Unit → Except AllocError (Scalar Prov) := fun _r =>
        Bind.bind (checkedSlice allocation range) fun bytes =>
          Bind.bind (readTargetUInt layout bytes) fun bits =>
            if readProvenance = true then
              have targetSize := pointerSize layout
              have kPtr : Unit → Except AllocError (Scalar Prov) := fun _r =>
                have kProv : Option Prov → Except AllocError (Scalar Prov) := fun provenance =>
                  match provenance with
                  | some provenance =>
                    have kFit : Unit → Except AllocError (Scalar Prov) := fun _r =>
                      Pure.pure (Scalar.fromPointer layout
                        (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat))))
                    if bits.toNat > 18446744073709551615 then
                      Bind.bind (throw (.pointerBitsDoNotFitOffset bits)) kFit
                    else kFit Unit.unit
                  | none =>
                    Except.mapError AllocError.scalar (Scalar.fromUInt bits range.size)
                match allocation.provenanceMap.readPtr range.start targetSize with
                | .ok provenance => Bind.bind (Pure.pure provenance) kProv
                | .error (.readPartialPointer offset) =>
                  Bind.bind (throw (.readPartialPointer offset)) kProv
                | .error reason => Bind.bind (throw (.provenance reason)) kProv
              if (range.size != targetSize) = true then
                Bind.bind (throw (.scalarPointerNotTargetSized range.size targetSize)) kPtr
              else kPtr Unit.unit
            else
              if PointerProvenance.offsetIsAddr (Prov := Prov) = true then
                Except.mapError AllocError.scalar (Scalar.fromUInt bits range.size)
              else
                Bind.bind
                  (Except.mapError AllocError.provenance
                    (allocation.provenanceMap.rangeEmpty range (pointerSize layout)))
                  fun isEmpty =>
                    if isEmpty = true then
                      Except.mapError AllocError.scalar (Scalar.fromUInt bits range.size)
                    else throw (.readPointerAsInt none)
      match res with
      | .error bad => Bind.bind (throw (.invalidUninitBytes (some ⟨range, bad⟩))) kMain
      | .ok () => kMain Unit.unit

private def writeScalarR (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar Prov) : EStateM AllocError (Miri.Memory.Allocation Prov Extra) Unit :=
  fun state =>
    Id.run
      (if (state.mutability != .Mut) = true then
         Pure.pure (.error .readOnlyAllocation state)
       else
         match value.toBitsOrPtrInternal range.size with
         | .ok converted =>
           Bind.bind (Pure.pure converted) fun bitsAndPointer =>
             match checkedSlice state range with
             | .error error => Pure.pure (.error error state)
             | .ok _ =>
               match state.initializationMask.setRange range true with
               | .ok mask =>
                 Bind.bind (Pure.pure mask) fun nextMask =>
                   have beforeClear := withInitMask state nextMask
                   match state.provenanceMap.clear range (raw state) (pointerSize layout) with
                   | .error reason mapAfter =>
                     Pure.pure (.error (.provenance reason) (withProvenance beforeClear mapAfter))
                   | .ok () clearedMap =>
                     have finish := range.start.bytes.toNat + range.size.bytes.toNat
                     have start := range.start.bytes.toNat
                     match
                       match bitsAndPointer with
                       | .bits bits => (bits, none)
                       | .pointer pointer => (BitVec.ofNat 128 pointer.offset.bytes.toNat, some pointer.provenance) with
                     | (bits, provenance) =>
                       match targetUIntBytes layout range.size bits with
                       | .ok data =>
                         Bind.bind (Pure.pure data) fun data =>
                           have bytes : Array UInt8 :=
                             (raw state).extract 0 start ++ data ++
                               (raw state).extract finish (raw state).size
                           if (bytes.size != state.byteSize.bytes.toNat) = true then
                             Pure.pure
                               (.error (.storageLengthMismatch state.byteSize bytes.size)
                                 (withProvenance beforeClear clearedMap))
                           else
                             have afterWrite := withRawBytes (withProvenance beforeClear clearedMap) bytes
                             match provenance with
                             | none => Pure.pure (.ok () afterWrite)
                             | some provenance =>
                               if (range.size != pointerSize layout) = true then
                                 Pure.pure
                                   (.error (.scalarPointerNotTargetSized range.size (pointerSize layout))
                                     afterWrite)
                               else
                                 match clearedMap.insertPtr range.start provenance (pointerSize layout) with
                                 | .error reason mapAfter =>
                                   Pure.pure (.error (.provenance reason) (withProvenance afterWrite mapAfter))
                                 | .ok () insertedMap =>
                                   Pure.pure (.ok () (withProvenance afterWrite insertedMap))
                       | .error error =>
                         Pure.pure (.error error (withProvenance beforeClear clearedMap))
               | .error error => Pure.pure (.error (.memory error) state)
         | .error reason => Pure.pure (.error (.scalar reason) state))


private theorem getBytesUnchecked_eq :
    @Miri.Memory.Allocation.getBytesUnchecked Prov Extra = @checkedSlice Prov Extra := rfl
private theorem fromBytes_eq_R :
    @Miri.Memory.Allocation.fromBytes Prov = @fromBytesR Prov := rfl
private theorem tryNew_eq_R :
    @Miri.Memory.Allocation.tryNew Prov = @tryNewR Prov := rfl
private theorem getBytesStripProvenance_eq_R :
    @Miri.Memory.Allocation.getBytesStripProvenance Prov Extra =
      @getBytesStripProvenanceR Prov Extra := rfl
private theorem readScalar_eq_R :
    @Miri.Memory.Allocation.readScalar Prov Extra = @readScalarR Prov Extra := rfl
private theorem writeScalar_eq_R :
    @Miri.Memory.Allocation.writeScalar Prov Extra = @writeScalarR Prov Extra := rfl
private theorem writeBytes_eq_R :
    @Miri.Memory.Allocation.writeBytes Prov Extra = @writeBytesR Prov Extra := rfl
private theorem writeUninit_eq_R :
    @Miri.Memory.Allocation.writeUninit Prov Extra = @writeUninitR Prov Extra := rfl
private theorem clearProvenance_eq_R :
    @Miri.Memory.Allocation.clearProvenance Prov Extra = @clearProvenanceR Prov Extra := rfl

end Allocation

end Mirrors

namespace Allocation
open Miri.ABI Miri.Memory
open Mirrors.Allocation
variable {P E E' : Type}

/-!
### 3c. Accessor lemmas for the mirrors and ported private `lean-miri` lemmas
-/

private theorem raw_withInitMask (a : Miri.Memory.Allocation P E) (m : InitMask) : raw (withInitMask a m) = raw a := rfl
private theorem byteSize_withInitMask (a : Miri.Memory.Allocation P E) (m : InitMask) : (withInitMask a m).byteSize = a.byteSize := rfl
private theorem provenanceMap_withInitMask (a : Miri.Memory.Allocation P E) (m : InitMask) : (withInitMask a m).provenanceMap = a.provenanceMap := rfl
private theorem raw_withProvenance (a : Miri.Memory.Allocation P E) (p : ProvenanceMap P) : raw (withProvenance a p) = raw a := rfl
private theorem byteSize_withProvenance (a : Miri.Memory.Allocation P E) (p : ProvenanceMap P) : (withProvenance a p).byteSize = a.byteSize := rfl
private theorem raw_mapExtra (a : Miri.Memory.Allocation P E) (f : E → E') : raw (a.mapExtra f) = raw a := rfl

private theorem le_maxU64Nat_of_lt {n : Nat} (h : n < HPow.hPow (2 : Nat) 64) :
    n ≤ Mirrors.maxU64Nat :=
  Nat.le_trans (Nat.le_pred_of_lt h) (by decide)

private theorem write_add_size (left right : Size)
    (fits : left.bytes.toNat + right.bytes.toNat < (HPow.hPow (2 : Nat) 64)) :
    Size.add left right = .ok (Size.ofBytes (left.bytes + right.bytes)) := by
  have noWrap : ¬left.bytes + right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    exact Nat.not_lt.mpr (Nat.le_add_right _ _)
  simp [Size.add, noWrap]

private theorem firstNonZero_replicate (n : Nat) : Mirrors.firstNonZero (Array.replicate n 0) = none := by
  let step : Nat → Option (Option (Nat × UInt8)) × Unit → Id (ForInStep (Option (Option (Nat × UInt8)) × Unit)) :=
    fun index _ => match (Array.replicate n 0)[index]? with
      | some byte => if byte != 0 then pure (.done (some (some (index, byte)), ())) else pure (.yield (none, ()))
      | none => pure (.done (some (some (index, 0)), ()))
  have scan : ∀ indices : List Nat, (∀ index, index ∈ indices → index < n) →
      forIn indices (none, ()) step = (none, ()) := by
    intro indices
    induction indices with
    | nil => intro good; rfl
    | cons head tail ih =>
      intro good
      have bound := good head (by simp)
      have atHead : (Array.replicate n (0 : UInt8))[head]? = some 0 := by simp [bound]
      rw [List.forIn_cons]
      simp only [step, atHead, pure, Pure.pure, bind, Bind.bind]
      exact ih (by intro index member; exact good index (by simp [member]))
  simp only [Mirrors.firstNonZero]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Array.size_replicate, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  dsimp only [step, Id.run, pure, Pure.pure] at scan
  rw [scan (List.range' 0 n) (by intro index member; simp only [List.mem_range', Nat.zero_add, Nat.one_mul] at member; let ⟨_, hi, heq⟩ := member; rw [heq]; exact hi)]

/-!
### 3d. The 37 Pass-1 `Miri.Memory.Allocation` specification theorems (and
helpers)
-/



private theorem checkedSlice_ok (allocation : Miri.Memory.Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    checkedSlice allocation range =
      .ok ((raw allocation).extract range.start.bytes.toNat finish.bytes.toNat) := by
  unfold checkedSlice
  change (raw allocation).size = allocation.byteSize.bytes.toNat at storage
  have h_not_s : ¬(finish.bytes < range.start.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr startLe)
  have h_not_f : ¬(allocation.byteSize.bytes < finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr inBounds)
  simp [storage, endEq, h_not_s, h_not_f, bind, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure]

private theorem full_range_endExclusive (sz : Size) :
    (allocRange Size.ZERO sz).endExclusive = .ok sz := by
  cases sz
  simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]

private theorem eq_of_not_bne {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : ¬((a != b) = true)) : a = b := by
  simp [bne] at h
  exact h

private theorem getBytesUnchecked_full_rawBytes (allocation : Miri.Memory.Allocation P E)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) :
    allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok (raw allocation) := by
  rw [getBytesUnchecked_eq]
  rw [checkedSlice_ok allocation (allocRange Size.ZERO allocation.byteSize) allocation.byteSize
    storage (full_range_endExclusive allocation.byteSize) (Nat.zero_le _) (Nat.le_refl _)]
  dsimp only [allocRange]
  have h_zero : Size.ZERO.bytes.toNat = 0 := rfl
  rw [h_zero, ← storage]
  exact congrArg Except.ok (Array.extract_size (xs := (raw allocation)))

private theorem extract_ByteAt (arr : Array UInt8) (start finish idx : Nat)
    (h_fin : finish ≤ arr.size) (h_lo : start ≤ idx) (h_hi : idx < finish) :
    (arr.extract start finish)[idx - start]? = arr[idx]? := by
  have h_idx_lt : idx < arr.size := Nat.lt_of_lt_of_le h_hi h_fin
  have h_ext_sz : (arr.extract start finish).size = finish - start := by
    simp [Array.size_extract, Nat.min_eq_left h_fin]
  have h_sub_lt : idx - start < (arr.extract start finish).size := by
    rw [h_ext_sz]; exact Nat.sub_lt_sub_right h_lo h_hi
  rw [Array.getElem?_eq_getElem h_sub_lt, Array.getElem?_eq_getElem h_idx_lt, Array.getElem_extract]
  have h_add_sub : start + (idx - start) = idx := Nat.add_sub_of_le h_lo
  simp [h_add_sub]

private theorem splice_getElem? (raw data : Array UInt8) (start finish k : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size)[k]? =
      if start ≤ k ∧ k < finish then data[k - start]? else raw[k]? := by
  let pfx := raw.extract 0 start
  let sfx := raw.extract finish raw.size
  have h_start_raw : start ≤ raw.size := Nat.le_trans h_lo h_fin
  have h_pfx_sz : pfx.size = start := by
    simp [pfx, Array.size_extract, Nat.min_eq_left h_start_raw]
  have h_sfx_sz : sfx.size = raw.size - finish := by
    simp [sfx, Array.size_extract]
  have h_pd_sz : (pfx ++ data).size = finish := by
    rw [Array.size_append, h_pfx_sz, h_data_sz, Nat.add_sub_of_le h_lo]
  cases Classical.em (k < start) with
  | inl h_lt_start =>
    have h_not_in : ¬(start ≤ k ∧ k < finish) := fun h => Nat.not_lt_of_le h.1 h_lt_start
    rw [if_neg_eq h_not_in]
    have h1 : (pfx ++ data ++ sfx)[k]? = (pfx ++ data)[k]? :=
      Array.getElem?_append_left (by rw [h_pd_sz]; exact Nat.lt_of_lt_of_le h_lt_start h_lo)
    have h2 : (pfx ++ data)[k]? = pfx[k]? :=
      Array.getElem?_append_left (by rw [h_pfx_sz]; exact h_lt_start)
    rw [h1, h2]
    have he := extract_ByteAt raw 0 start k h_start_raw (Nat.zero_le _) h_lt_start
    have _h := he; simp only [Nat.sub_zero] at _h; exact _h
  | inr h_lt_start =>
    have h_ge_start : start ≤ k := Nat.le_of_not_lt h_lt_start
    cases Classical.em (k < finish) with
    | inl h_lt_fin =>
      have h_in : start ≤ k ∧ k < finish := ⟨h_ge_start, h_lt_fin⟩
      rw [if_pos_eq h_in]
      have h1 : (pfx ++ data ++ sfx)[k]? = (pfx ++ data)[k]? :=
        Array.getElem?_append_left (by rw [h_pd_sz]; exact h_lt_fin)
      have h2 : (pfx ++ data)[k]? = data[k - pfx.size]? :=
        Array.getElem?_append_right (by rw [h_pfx_sz]; exact h_ge_start)
      have _h := h1.trans h2
      rw [h_pfx_sz] at _h; exact _h
    | inr h_lt_fin =>
      have h_ge_fin : finish ≤ k := Nat.le_of_not_lt h_lt_fin
      have h_not_in : ¬(start ≤ k ∧ k < finish) := fun h => h_lt_fin h.2
      rw [if_neg_eq h_not_in]
      have h1 : (pfx ++ data ++ sfx)[k]? = sfx[k - (pfx ++ data).size]? :=
        Array.getElem?_append_right (by rw [h_pd_sz]; exact h_ge_fin)
      rw [h1, h_pd_sz]
      cases Classical.em (k < raw.size) with
      | inl h_lt_raw =>
        exact extract_ByteAt raw finish raw.size k (Nat.le_refl _) h_ge_fin h_lt_raw
      | inr h_lt_raw =>
        have h_none1 : sfx[k - finish]? = none :=
          Array.getElem?_eq_none (by rw [h_sfx_sz]; exact Nat.sub_le_sub_right (Nat.le_of_not_lt h_lt_raw) finish)
        have h_none2 : raw[k]? = none :=
          Array.getElem?_eq_none (Nat.le_of_not_lt h_lt_raw)
        exact h_none1.trans h_none2.symm

private theorem splice_extract_exact (raw data : Array UInt8) (start finish : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size).extract start finish = data := by
  let spliced := raw.extract 0 start ++ data ++ raw.extract finish raw.size
  have h_sp_sz : spliced.size = raw.size := by
    have h_st : start ≤ raw.size := Nat.le_trans h_lo h_fin
    simp only [spliced, Array.size_append, Array.size_extract, Nat.min_eq_left h_st,
      Nat.min_self, Nat.sub_zero, h_data_sz]
    rw [Nat.add_sub_of_le h_lo, Nat.add_sub_of_le h_fin]
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Nat.min_eq_left h_fin, h_data_sz]
  · intro i hi1 hi2
    have hi_lt : i < finish - start := by rw [h_data_sz] at hi2; exact hi2
    have h_lo_i : start ≤ start + i := Nat.le_add_right start i
    have h_hi_i : start + i < finish := add_lt_of_lt_sub_left hi_lt
    have h_eq? := extract_ByteAt spliced start finish (start + i) (by rw [h_sp_sz]; exact h_fin)
      h_lo_i h_hi_i
    have h_sub : start + i - start = i := Nat.add_sub_cancel_left start i
    rw [h_sub] at h_eq?
    have h_sp_i := splice_getElem? raw data start finish (start + i) h_lo h_fin h_data_sz
    rw [if_pos_eq ⟨h_lo_i, h_hi_i⟩, h_sub] at h_sp_i
    have h_lhs : (spliced.extract start finish)[i]? = some (GetElem.getElem (spliced.extract start finish) i hi1) :=
      Array.getElem?_eq_getElem hi1
    have h_rhs : data[i]? = some (GetElem.getElem data i hi2) := Array.getElem?_eq_getElem hi2
    have h_comb : (spliced.extract start finish)[i]? = data[i]? := h_eq?.trans h_sp_i
    exact Option.some.inj (h_lhs.symm.trans (h_comb.trans h_rhs))

private theorem splice_extract_disjoint (raw data : Array UInt8) (wStart wFin qStart qFin : Nat)
    (h_w_lo : wStart ≤ wFin) (h_w_fin : wFin ≤ raw.size)
    (_h_q_lo : qStart ≤ qFin) (h_q_fin : qFin ≤ raw.size)
    (h_data_sz : data.size = wFin - wStart)
    (h_disj : wFin ≤ qStart ∨ qFin ≤ wStart) :
    (raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size).extract qStart qFin =
      raw.extract qStart qFin := by
  let spliced := raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size
  have h_sp_sz : spliced.size = raw.size := by
    have h_ws : wStart ≤ raw.size := Nat.le_trans h_w_lo h_w_fin
    simp only [spliced, Array.size_append, Array.size_extract, Nat.min_eq_left h_ws,
      Nat.min_self, Nat.sub_zero, h_data_sz]
    rw [Nat.add_sub_of_le h_w_lo, Nat.add_sub_of_le h_w_fin]
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Array.size_extract]
  · intro i hi1 hi2
    have hi_lt : i < qFin - qStart := by
      rw [Array.size_extract, Nat.min_eq_left h_q_fin] at hi2
      exact hi2
    have h_sub : qStart + i - qStart = i := Nat.add_sub_cancel_left qStart i
    have h_qlo_i : qStart ≤ qStart + i := Nat.le_add_right qStart i
    have h_qhi_i : qStart + i < qFin := add_lt_of_lt_sub_left hi_lt
    have h_eq1 := extract_ByteAt spliced qStart qFin (qStart + i) (by rw [h_sp_sz]; exact h_q_fin)
      h_qlo_i h_qhi_i
    have h_eq2 := extract_ByteAt raw qStart qFin (qStart + i) h_q_fin h_qlo_i h_qhi_i
    have h_sp_i := splice_getElem? raw data wStart wFin (qStart + i) h_w_lo h_w_fin h_data_sz
    have h_out : ¬(wStart ≤ qStart + i ∧ qStart + i < wFin) := fun h_in =>
      Or.elim h_disj
        (fun h => Nat.not_lt_of_le (Nat.le_trans h h_qlo_i) h_in.2)
        (fun h => Nat.not_le_of_lt (Nat.lt_of_lt_of_le h_qhi_i h) h_in.1)
    rw [if_neg_eq h_out] at h_sp_i
    have h_comb : (spliced.extract qStart qFin)[i]? = (raw.extract qStart qFin)[i]? := by
      have _h_simpa := (h_eq1.trans h_sp_i).trans h_eq2.symm
      simp [h_sub] at _h_simpa
      exact _h_simpa
    have h_lhs := Array.getElem?_eq_getElem hi1
    have h_rhs := Array.getElem?_eq_getElem hi2
    exact Option.some.inj (h_lhs.symm.trans (h_comb.trans h_rhs))

/-- `withExtra` preserves `byteSize`. -/
theorem byteSize_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).byteSize = allocation.byteSize := rfl

/-- `withExtra` preserves the byte-storage length. -/
theorem len_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).len = allocation.len := rfl

/-- `withExtra` preserves the alignment. -/
theorem align_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).align = allocation.align := rfl

/-- `withExtra` preserves the mutability. -/
theorem mutability_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).mutability = allocation.mutability := rfl

/-- `withExtra` preserves the provenance map. -/
theorem provenanceMap_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).provenanceMap = allocation.provenanceMap := rfl

/-- `withExtra` preserves the initialization mask. -/
theorem initializationMask_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).initializationMask = allocation.initializationMask := rfl

/-- `withExtra` does not affect `getBytesUnchecked`. -/
theorem getBytesUnchecked_withExtra (allocation : Miri.Memory.Allocation P Unit) (extra : E) (range : AllocRange) :
    (allocation.withExtra extra).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

/-- `mapExtra` preserves `byteSize`. -/
theorem byteSize_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    (allocation.mapExtra f).byteSize = allocation.byteSize := rfl

/-- `mapExtra` preserves the byte-storage length. -/
theorem len_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    (allocation.mapExtra f).len = allocation.len := rfl

/-- `mapExtra` preserves the alignment. -/
theorem align_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    (allocation.mapExtra f).align = allocation.align := rfl

/-- `mapExtra` preserves the mutability. -/
theorem mutability_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    (allocation.mapExtra f).mutability = allocation.mutability := rfl

/-- `mapExtra` preserves the provenance map. -/
theorem provenanceMap_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    (allocation.mapExtra f).provenanceMap = allocation.provenanceMap := rfl

/-- `mapExtra` preserves the initialization mask. -/
theorem initializationMask_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    (allocation.mapExtra f).initializationMask = allocation.initializationMask := rfl

/-- `mapExtra` does not affect `getBytesUnchecked`. -/
theorem getBytesUnchecked_mapExtra (allocation : Miri.Memory.Allocation P E) (f : E → E') (range : AllocRange) :
    (allocation.mapExtra f).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

/-- `mapExtra` does not affect `getBytesStripProvenance`. -/
theorem getBytesStripProvenance_mapExtra [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (f : E → E') (layout : TargetDataLayout) (range : AllocRange) :
    (allocation.mapExtra f).getBytesStripProvenance layout range =
      allocation.getBytesStripProvenance layout range := rfl

/-- `mapExtra` does not affect `readScalar`. -/
theorem readScalar_mapExtra [DecidableEq P] [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (f : E → E') (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    (allocation.mapExtra f).readScalar layout range readProvenance =
      allocation.readScalar layout range readProvenance := rfl

/-- `writeBytes` commutes with `mapExtra`: running it on `allocation.mapExtra f`
yields the same outcome as running it on `allocation`, with `mapExtra f` applied
to the resulting state (on success and on error). -/
theorem writeBytes_mapExtra (start : Size) (bytes : Array UInt8) (ptrSize : Size)
    (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    Miri.Memory.Allocation.writeBytes start bytes ptrSize (allocation.mapExtra f) =
      (match Miri.Memory.Allocation.writeBytes start bytes ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : ∀ r, checkedSlice (allocation.mapExtra f) r = checkedSlice allocation r := fun _ => rfl
  rw [writeBytes_eq_R, writeBytes_eq_R]
  unfold writeBytesR setInitialization overwriteRawBytes
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.mapError, Except.pure, slices,
    mutability_mapExtra, initializationMask_mapExtra, raw_withProvenance, byteSize_withProvenance]
  cases Mirrors.sizeForArray bytes.size with
  | error e => rfl
  | ok writeSize =>
    dsimp only
    cases checkedSlice allocation (allocRange start writeSize) with
    | error e => rfl
    | ok _ =>
      dsimp only
      cases Classical.em (writeSize.bytes == 0) with
      | inl h0 =>
        simp only [h0, reduceIte]
      | inr h0 =>
        simp only [h0, Bool.false_eq_true, reduceIte]
        cases Classical.em (allocation.mutability != .Mut) with
        | inl hm =>
          simp only [hm, reduceIte]
        | inr hm =>
          simp only [hm, Bool.false_eq_true, reduceIte]
          cases allocation.initializationMask.setRange (allocRange start writeSize) true with
          | error e => rfl
          | ok mask =>
            dsimp only
            simp only [raw_mapExtra, provenanceMap_mapExtra, byteSize_mapExtra,
              raw_withInitMask, byteSize_withInitMask, provenanceMap_withInitMask]
            cases allocation.provenanceMap.clear (allocRange start writeSize) (raw allocation) ptrSize with
            | error e pm => rfl
            | ok _ pm =>
              dsimp only
              cases (allocRange start writeSize).endExclusive with
              | error e => rfl
              | ok fin =>
                dsimp only
                cases Classical.em ((((raw allocation).extract 0 (allocRange start writeSize).start.bytes.toNat ++ bytes ++ (raw allocation).extract fin.bytes.toNat).size != allocation.byteSize.bytes.toNat) = true) with
                | inl h_len => simp only [h_len, reduceIte]; rfl
                | inr h_len => simp only [h_len, Bool.false_eq_true, reduceIte]; rfl

/-- `clearProvenance` commutes with `mapExtra`: running it on
`allocation.mapExtra f` yields the same outcome as running it on `allocation`,
with `mapExtra f` applied to the resulting state (on success and on error). -/
theorem clearProvenance_mapExtra (range : AllocRange) (ptrSize : Size)
    (allocation : Miri.Memory.Allocation P E) (f : E → E') :
    Miri.Memory.Allocation.clearProvenance range ptrSize (allocation.mapExtra f) =
      (match Miri.Memory.Allocation.clearProvenance range ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : checkedSlice (allocation.mapExtra f) range = checkedSlice allocation range := rfl
  rw [clearProvenance_eq_R, clearProvenance_eq_R]
  unfold clearProvenanceR
  rw [slices]
  simp only [raw_mapExtra, provenanceMap_mapExtra]
  cases checkedSlice allocation range with
  | error _ => rfl
  | ok _ =>
    dsimp only
    cases allocation.provenanceMap.clear range (raw allocation) ptrSize <;> rfl

private theorem replicate_extract_zero (n start finish : Nat)
    (_h_lo : start ≤ finish) (h_fin : finish ≤ n) :
    (Array.replicate n (0 : UInt8)).extract start finish = Array.replicate (finish - start) 0 := by
  apply Array.ext
  · simp [Array.size_replicate, Nat.min_eq_left h_fin]
  · intro i hi1 hi2
    rw [Array.getElem_extract, Array.getElem_replicate, Array.getElem_replicate]

/--
A successful `fromBytes` produces an allocation of exactly `bytes.size` bytes
with the requested mutability, unit extra, no native buffer, empty provenance,
and a well-formed fully initialized mask, whose in-bounds slices are the
corresponding slices of `bytes`.
-/
theorem fromBytes_spec (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (alloc : Miri.Memory.Allocation P Unit)
    (created : Miri.Memory.Allocation.fromBytes bytes align mutability = .ok alloc) :
    alloc.byteSize.bytes.toNat = bytes.size ∧
      alloc.len = bytes.size ∧
      alloc.mutability = mutability ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new alloc.byteSize true ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ bytes.size →
        alloc.getBytesUnchecked range =
          .ok (bytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  rw [fromBytes_eq_R] at created
  unfold fromBytesR at created
  cases h_al : Mirrors.checkedAlign align with
  | error e => simp [h_al, bind, Bind.bind, Except.bind] at created
  | ok normAlign =>
    simp only [h_al, bind, Bind.bind, Except.bind] at created
    cases h_sz : Mirrors.sizeForArray bytes.size with
    | error e => simp [h_sz] at created
    | ok sz =>
      simp only [h_sz] at created
      cases Classical.em (bytes.size = sz.bytes.toNat) with
      | inl h_eq =>
        simp only [h_eq, reduceDIte, pure, Pure.pure, Except.pure, Except.ok.injEq] at created
        subst created
        refine ⟨h_eq.symm, rfl, rfl, rfl, rfl, rfl, rfl, True.intro, ?_⟩
        intro range finish h_end h_lo h_fin
        exact checkedSlice_ok _ range finish h_eq h_end h_lo
          (by change _ ≤ sz.bytes.toNat; rw [← h_eq]; exact h_fin)
      | inr h_eq =>
        simp [h_eq] at created

/--
`fromBytes` succeeds for every byte array that fits in `u64` once the alignment
is normalized (`Align.bytes` and `Align.fromBytes` round-trip), with
`byteSize = bytes.size` and the given alignment.
-/
theorem fromBytes_exists (bytes : Array UInt8) (align : Align) (alignmentBytes : UInt64)
    (mutability : Mutability)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align)
    (h_fits : bytes.size < (HPow.hPow (2 : Nat) 64)) :
    ∃ alloc : Miri.Memory.Allocation P Unit,
      Miri.Memory.Allocation.fromBytes bytes align mutability = .ok alloc ∧
      alloc.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      alloc.align = align := by
  have h_ca : Mirrors.checkedAlign align = .ok align := by
    unfold Mirrors.checkedAlign
    simp [h_bytes, h_norm, bind, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure]
  have h_not_gt : ¬(bytes.size > Mirrors.maxU64Nat) := Nat.not_lt.mpr (le_maxU64Nat_of_lt h_fits)
  have h_tonat : (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat = bytes.size := by
    simp [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_fits]
  have h_sfa : Mirrors.sizeForArray bytes.size = .ok (Size.ofBytes (UInt64.ofNat bytes.size)) := by
    unfold Mirrors.sizeForArray
    simp [h_not_gt, h_tonat, pure, Pure.pure, Except.pure]
  refine ⟨mkAlloc bytes (Size.ofBytes (UInt64.ofNat bytes.size)) ProvenanceMap.new
    (InitMask.new (Size.ofBytes (UInt64.ofNat bytes.size)) true) align mutability () none,
    ?_, rfl, rfl⟩
  rw [fromBytes_eq_R]
  unfold fromBytesR
  simp [h_ca, h_sfa, h_tonat, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/--
A successful `tryNew` with zeroed host storage produces a mutable allocation of
`size` zero bytes with unit extra, no native buffer, empty provenance, and a
well-formed mask that is `InitMask.new size false` for `.Uninit` and
`InitMask.new size true` for `.Zero`, whose in-bounds slices read back zero
bytes.
-/
theorem tryNew_spec (size : Size) (align : Align) (init : AllocInit)
    (alloc : Miri.Memory.Allocation P Unit)
    (created : Miri.Memory.Allocation.tryNew size align init
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc) :
    alloc.byteSize = size ∧
      alloc.len = size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      (init = .Uninit → alloc.initializationMask = InitMask.new size false) ∧
      (init = .Zero → alloc.initializationMask = InitMask.new size true) ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ size.bytes.toNat →
        alloc.getBytesUnchecked range =
          .ok (Array.replicate (finish.bytes.toNat - range.start.bytes.toNat) 0) := by
  rw [tryNew_eq_R] at created
  unfold tryNewR at created
  cases h_al : Mirrors.checkedAlign align with
  | error e => simp [h_al, bind, Bind.bind, Except.bind] at created
  | ok normAlign =>
    let bInit := match init with | .Uninit => false | .Zero => true
    simp [h_al, firstNonZero_replicate,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at created
    subst created
    refine ⟨rfl, Array.size_replicate, rfl, rfl, rfl, rfl,
      fun h => by subst h; rfl, fun h => by subst h; rfl, True.intro, ?_⟩
    intro range finish h_end h_lo h_fin
    let a0 : Miri.Memory.Allocation P Unit :=
      mkAlloc (Array.replicate size.bytes.toNat 0) size ProvenanceMap.new
        (InitMask.new size bInit) normAlign .Mut () none
    rw [getBytesUnchecked_eq]
    rw [checkedSlice_ok a0 range finish Array.size_replicate h_end h_lo h_fin]
    exact congrArg Except.ok (replicate_extract_zero size.bytes.toNat _ _ h_lo h_fin)

/--
`tryNew` with zeroed host storage succeeds for every size once the alignment is
normalized, with the given alignment.
-/
theorem tryNew_exists (size : Size) (align : Align) (alignmentBytes : UInt64) (init : AllocInit)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align) :
    ∃ alloc : Miri.Memory.Allocation P Unit,
      Miri.Memory.Allocation.tryNew size align init
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      alloc.align = align := by
  refine ⟨mkAlloc (Array.replicate size.bytes.toNat 0) size ProvenanceMap.new
    (InitMask.new size (match init with | .Uninit => false | .Zero => true)) align .Mut () none,
    ?_, rfl⟩
  rw [tryNew_eq_R]
  simp [tryNewR, Mirrors.checkedAlign, h_bytes, h_norm, firstNonZero_replicate,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

/--
On a storage-consistent allocation, an in-bounds `getBytesUnchecked` succeeds
and returns exactly `finish - start` bytes.
-/
theorem getBytesUnchecked_size (allocation : Miri.Memory.Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ slice, allocation.getBytesUnchecked range = .ok slice ∧
      slice.size = finish.bytes.toNat - range.start.bytes.toNat := by
  refine ⟨(raw allocation).extract range.start.bytes.toNat finish.bytes.toNat,
    checkedSlice_ok allocation range finish storage endEq startLe inBounds, ?_⟩
  change _ = _
  have h_fin_raw : finish.bytes.toNat ≤ (raw allocation).size := by
    change finish.bytes.toNat ≤ allocation.len; rw [storage]; exact inBounds
  simp [Array.size_extract, Nat.min_eq_left h_fin_raw]

/--
Reading a sub-range equals extracting the corresponding sub-slice of the bytes
read for an enclosing range.
-/
theorem getBytesUnchecked_subrange (allocation : Miri.Memory.Allocation P E)
    (rOuter rInner : AllocRange) (fOuter fInner : Size) (outerBytes : Array UInt8)
    (h_outer_end : rOuter.endExclusive = .ok fOuter)
    (h_inner_end : rInner.endExclusive = .ok fInner)
    (h_lo : rOuter.start.bytes.toNat ≤ rInner.start.bytes.toNat)
    (h_mid : rInner.start.bytes.toNat ≤ fInner.bytes.toNat)
    (h_hi : fInner.bytes.toNat ≤ fOuter.bytes.toNat)
    (h_outer : allocation.getBytesUnchecked rOuter = .ok outerBytes) :
    allocation.getBytesUnchecked rInner =
      .ok (outerBytes.extract
        (rInner.start.bytes.toNat - rOuter.start.bytes.toNat)
        (fInner.bytes.toNat - rOuter.start.bytes.toNat)) := by
  rw [getBytesUnchecked_eq] at h_outer
  unfold checkedSlice at h_outer
  cases Classical.em ((raw allocation).size != allocation.byteSize.bytes.toNat) with
  | inl h_mis =>
    simp [h_mis] at h_outer
  | inr h_mis =>
    have h_raw_sz : (raw allocation).size = allocation.byteSize.bytes.toNat := eq_of_not_bne h_mis
    have storage : allocation.len = allocation.byteSize.bytes.toNat := h_raw_sz
    simp only [h_mis, Bool.false_eq_true, reduceIte, h_outer_end, Except.mapError,
      bind, Bind.bind, Except.bind] at h_outer
    cases Classical.em (rOuter.start.bytes > fOuter.bytes || fOuter.bytes > allocation.byteSize.bytes) with
    | inl h_oob =>
      simp [h_oob] at h_outer
    | inr h_oob =>
      simp only [h_oob, Bool.false_eq_true, reduceIte, pure, Pure.pure, Except.pure,
        Except.ok.injEq] at h_outer
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      have h_fOuter_le : fOuter.bytes.toNat ≤ allocation.byteSize.bytes.toNat := Nat.le_of_not_lt h_oob.2
      have h_fOuter_raw : fOuter.bytes.toNat ≤ (raw allocation).size := by rw [h_raw_sz]; exact h_fOuter_le
      have h_fInner_le : fInner.bytes.toNat ≤ allocation.byteSize.bytes.toNat := Nat.le_trans h_hi h_fOuter_le
      have h_fInner_raw : fInner.bytes.toNat ≤ (raw allocation).size := by rw [h_raw_sz]; exact h_fInner_le
      rw [getBytesUnchecked_eq]
      rw [checkedSlice_ok allocation rInner fInner storage h_inner_end h_mid h_fInner_le]
      subst h_outer
      apply congrArg Except.ok
      apply Array.ext
      · simp only [Array.size_extract, Nat.min_eq_left h_fOuter_raw, Nat.min_eq_left h_fInner_raw,
          Nat.min_eq_left (Nat.sub_le_sub_right h_hi rOuter.start.bytes.toNat)]
        exact (nat_sub_sub_sub_cancel_right h_lo h_mid).symm
      · intro i hi1 hi2
        rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_extract]
        have h_idx_eq : rOuter.start.bytes.toNat + ((rInner.start.bytes.toNat - rOuter.start.bytes.toNat) + i) =
            rInner.start.bytes.toNat + i := by
          rw [← Nat.add_assoc, Nat.add_sub_of_le h_lo]
        simp only [h_idx_eq]

/--
Reading two adjacent ranges and concatenating the results equals reading their
union.
-/
theorem getBytesUnchecked_split (allocation : Miri.Memory.Allocation P E)
    (r1 r2 r12 : AllocRange) (mid fin : Size) (b1 b2 : Array UInt8)
    (h_end1 : r1.endExclusive = .ok mid)
    (h_start2 : r2.start = mid)
    (h_end2 : r2.endExclusive = .ok fin)
    (h_start12 : r12.start = r1.start)
    (h_end12 : r12.endExclusive = .ok fin)
    (h_lo1 : r1.start.bytes.toNat ≤ mid.bytes.toNat)
    (h_lo2 : mid.bytes.toNat ≤ fin.bytes.toNat)
    (h_get1 : allocation.getBytesUnchecked r1 = .ok b1)
    (h_get2 : allocation.getBytesUnchecked r2 = .ok b2) :
    allocation.getBytesUnchecked r12 = .ok (b1 ++ b2) := by
  have h_chk2 := h_get2
  rw [getBytesUnchecked_eq] at h_chk2
  unfold checkedSlice at h_chk2
  cases Classical.em ((raw allocation).size != allocation.byteSize.bytes.toNat) with
  | inl h_mis =>
    simp [h_mis] at h_chk2
  | inr h_mis =>
    have h_raw_sz : (raw allocation).size = allocation.byteSize.bytes.toNat := eq_of_not_bne h_mis
    have storage : allocation.len = allocation.byteSize.bytes.toNat := h_raw_sz
    simp only [h_mis, Bool.false_eq_true, reduceIte, h_end2, Except.mapError,
      bind, Bind.bind, Except.bind] at h_chk2
    cases Classical.em (r2.start.bytes > fin.bytes || fin.bytes > allocation.byteSize.bytes) with
    | inl h_oob =>
      simp [h_oob] at h_chk2
    | inr h_oob =>
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      have h_fin_ib : fin.bytes.toNat ≤ allocation.byteSize.bytes.toNat := Nat.le_of_not_lt h_oob.2
      have h_fin_raw : fin.bytes.toNat ≤ (raw allocation).size := by rw [h_raw_sz]; exact h_fin_ib
      have h_mid_ib : mid.bytes.toNat ≤ allocation.byteSize.bytes.toNat := Nat.le_trans h_lo2 h_fin_ib
      have h_mid_raw : mid.bytes.toNat ≤ (raw allocation).size := by rw [h_raw_sz]; exact h_mid_ib
      have hs1 := checkedSlice_ok allocation r1 mid storage h_end1 h_lo1 h_mid_ib
      have hs2 := checkedSlice_ok allocation r2 fin storage h_end2 (by rw [h_start2]; exact h_lo2) h_fin_ib
      have hs12 := checkedSlice_ok allocation r12 fin storage h_end12 (by rw [h_start12]; exact Nat.le_trans h_lo1 h_lo2) h_fin_ib
      rw [getBytesUnchecked_eq] at h_get1 h_get2
      rw [getBytesUnchecked_eq]
      rw [hs1] at h_get1
      rw [hs2] at h_get2
      injection h_get1 with hb1
      injection h_get2 with hb2
      subst hb1; subst hb2
      rw [hs12, h_start12, h_start2]
      apply congrArg Except.ok
      apply Array.ext
      · simp only [Array.size_extract, Array.size_append, Nat.min_eq_left h_fin_raw, Nat.min_eq_left h_mid_raw]
        have h_cancel : (mid.bytes.toNat - r1.start.bytes.toNat) + (fin.bytes.toNat - mid.bytes.toNat) =
            fin.bytes.toNat - r1.start.bytes.toNat :=
          nat_sub_add_sub_cancel h_lo1 h_lo2
        exact h_cancel.symm
      · intro i hi1 hi2
        have hi_lt : i < fin.bytes.toNat - r1.start.bytes.toNat := by
          rw [Array.size_extract, Nat.min_eq_left h_fin_raw] at hi1; exact hi1
        have h_sz1 : ((raw allocation).extract r1.start.bytes.toNat mid.bytes.toNat).size =
            mid.bytes.toNat - r1.start.bytes.toNat := by
          simp [Array.size_extract, Nat.min_eq_left h_mid_raw]
        cases Classical.em (i < mid.bytes.toNat - r1.start.bytes.toNat) with
        | inl h_left =>
          rw [Array.getElem_append_left (by rw [h_sz1]; exact h_left),
            Array.getElem_extract, Array.getElem_extract]
        | inr h_left =>
          rw [Array.getElem_append_right (by rw [h_sz1]; exact Nat.le_of_not_lt h_left),
            Array.getElem_extract, Array.getElem_extract]
          have h_idx_eq : mid.bytes.toNat +
              (i - ((raw allocation).extract r1.start.bytes.toNat mid.bytes.toNat).size) =
              r1.start.bytes.toNat + i := by
            rw [h_sz1]
            have h_ge := Nat.le_of_not_lt h_left
            have h_eq1 : mid.bytes.toNat - r1.start.bytes.toNat + (i - (mid.bytes.toNat - r1.start.bytes.toNat)) = i :=
              Nat.add_sub_of_le h_ge
            have h_add : r1.start.bytes.toNat + i = mid.bytes.toNat + (i - (mid.bytes.toNat - r1.start.bytes.toNat)) := by
              have h2 : r1.start.bytes.toNat + i =
                  r1.start.bytes.toNat + ((mid.bytes.toNat - r1.start.bytes.toNat) + (i - (mid.bytes.toNat - r1.start.bytes.toNat))) :=
                congrArg (r1.start.bytes.toNat + ·) h_eq1.symm
              rw [h2, ← Nat.add_assoc, Nat.add_sub_of_le h_lo1]
            exact h_add.symm
          simp only [h_idx_eq]

private theorem targetUIntBytes_eq_ofFn (layout : TargetDataLayout) (size : Size) (bits : U128)
    (limit : size.bytes.toNat ≤ 16) :
    Mirrors.targetUIntBytes layout size bits =
      .ok (Array.ofFn (fun i : Fin size.bytes.toNat =>
        UInt8.ofNat ((HMod.hMod ((HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then i.1 else size.bytes.toNat - i.1 - 1))))) 256)))) := by
  let byteFn : Nat → UInt8 := fun index =>
    UInt8.ofNat ((HMod.hMod ((HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))))) 256))
  have h_loop : ∀ (indices : List Nat) (acc : Array UInt8),
      (forIn indices acc (fun index cur =>
        (Except.ok (ForInStep.yield (cur.push (byteFn index))) :
          Except AllocError (ForInStep (Array UInt8))))) =
      .ok (acc ++ (indices.map byteFn).toArray) := by
    intro indices
    induction indices with
    | nil =>
      intro acc
      simp [List.forIn_nil, Pure.pure, Except.pure]
    | cons idx rest ih =>
      intro acc
      rw [List.forIn_cons]
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [ih (acc.push (byteFn idx))]
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_append]
      · intro k hk1 hk2
        cases Classical.em (k < acc.size) with
        | inl hk =>
          rw [Array.getElem_append_left (by simp [Array.size_push]; exact Nat.lt_succ_of_lt hk),
            Array.getElem_push_lt hk, Array.getElem_append_left hk]
        | inr hk =>
          cases Classical.em (k = acc.size) with
          | inl hk_eq =>
            subst hk_eq
            rw [Array.getElem_append_left (by simp [Array.size_push]),
              Array.getElem_push_eq, Array.getElem_append_right (Nat.le_refl _)]
            simp
          | inr hk_eq =>
            have h_ge : acc.size + 1 ≤ k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hk) (Ne.symm hk_eq)
            rw [Array.getElem_append_right (by simp [Array.size_push]; exact h_ge),
              Array.getElem_append_right (Nat.le_of_not_lt hk)]
            simp only [Array.size_push, List.map_cons, List.getElem_toArray, List.getElem_cons]
            have h_pos : k - acc.size = (k - (acc.size + 1)) + 1 :=
              (Nat.sub_eq_iff_eq_add (Nat.le_of_not_lt hk)).mpr
                (by rw [Nat.add_assoc, Nat.add_comm 1 acc.size, Nat.sub_add_cancel h_ge])
            simp [h_pos]
  have small : ¬size.bytes > 16 := by
    simp only [UInt64.lt_iff_toNat_lt]
    exact Nat.not_lt.mpr limit
  unfold Mirrors.targetUIntBytes
  simp only [small, reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_inst := h_loop (List.range' 0 ({ stop := size.bytes.toNat, step_pos := Nat.zero_lt_one } : Std.Legacy.Range).size) List.nil.toArray
  dsimp only [byteFn] at h_inst
  change (Bind.bind (forIn (List.range' 0 ({ stop := size.bytes.toNat, step_pos := Nat.zero_lt_one } : Std.Legacy.Range).size) List.nil.toArray (fun index cur =>
    Except.ok (ForInStep.yield (cur.push (UInt8.ofNat ((HMod.hMod ((HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))))) 256)))))))
    Except.ok) = _
  rw [h_inst]
  simp only [Bind.bind, Except.bind, Array.empty_append]
  apply congrArg Except.ok
  apply Array.ext
  · simp [Std.Legacy.Range.size]
  · intro i hi1 hi2
    simp [List.getElem_range']

private theorem readTargetUInt_eq_foldl (layout : TargetDataLayout) (bytes : Array UInt8)
    (limit : bytes.size ≤ 16) :
    Mirrors.readTargetUInt layout bytes =
      .ok (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc index =>
        acc + (bytes[index]?.getD 0).toNat * (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then index else bytes.size - index - 1)))) 0)) := by
  have h_loop : ∀ (indices : List Nat) (acc : Nat),
      (∀ idx, idx ∈ indices → idx < bytes.size) →
      (forIn indices acc (fun index value =>
        (match bytes[index]? with
          | some byte =>
            pure (ForInStep.yield (value + byte.toNat * (HPow.hPow (2 : Nat) (8 *
              (if layout.endian == .little then index else bytes.size - index - 1)))))
          | _ =>
            Bind.bind (throw (α := Unit) (.invalidSliceEndpoints index (index + 1) bytes.size)) fun _ =>
              Pure.pure (ForInStep.yield value) :
          Except AllocError (ForInStep Nat)))) =
      .ok (indices.foldl (fun v index =>
        v + (bytes[index]?.getD 0).toNat * (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then index else bytes.size - index - 1)))) acc) := by
    intro indices
    induction indices with
    | nil =>
      intro acc _
      rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < bytes.size := h_in idx (List.mem_cons_self)
      have h_get : bytes[idx]? = some (GetElem.getElem bytes idx h_ib) := Array.getElem?_eq_getElem h_ib
      rw [List.forIn_cons, List.foldl_cons]
      simp only [h_get, Option.getD_some, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  have small : ¬bytes.size > 16 := Nat.not_lt.mpr limit
  unfold Mirrors.readTargetUInt
  simp only [small, reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_rng_eq : List.range'
      (Std.Legacy.Range.mk 0 bytes.size 1 Nat.zero_lt_one).start
      (Std.Legacy.Range.mk 0 bytes.size 1 Nat.zero_lt_one).size
      (Std.Legacy.Range.mk 0 bytes.size 1 Nat.zero_lt_one).step =
      List.range bytes.size := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  rw [h_rng_eq]
  rw [h_loop (List.range bytes.size) 0 (fun idx h => List.mem_range.mp h)]
  rfl

private theorem digit_step_mod (val m : Nat) :
    (HMod.hMod val (HPow.hPow (2 : Nat) (8 * m))) + ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * m)))) 256)) * (HPow.hPow (2 : Nat) (8 * m)) =
      (HMod.hMod val (HPow.hPow (2 : Nat) (8 * (m + 1)))) := by
  let P := (HPow.hPow (2 : Nat) (8 * m))
  have hP_pos : 0 < P := Nat.two_pow_pos (8 * m)
  let r := (HMod.hMod val P)
  let d := (HMod.hMod ((HDiv.hDiv val P)) 256)
  let q := (HDiv.hDiv ((HDiv.hDiv val P)) 256)
  have hr : r < P := Nat.mod_lt val hP_pos
  have hd : d < 256 := Nat.mod_lt _ (by decide)
  have hd_le : d ≤ 255 := Nat.le_pred_of_lt hd
  have h_dp : d * P ≤ 255 * P := Nat.mul_le_mul_right P hd_le
  have h_sum_lt : r + d * P < P * 256 := by
    have h_lt : r + d * P < P + 255 * P := Nat.add_lt_add_of_lt_of_le hr h_dp
    rw [Nat.add_comm P (255 * P)] at h_lt
    rw [← Nat.succ_mul 255 P, Nat.mul_comm 256 P] at h_lt; exact h_lt
  have h_div1 : P * ((HDiv.hDiv val P)) + r = val := Nat.div_add_mod val P
  have h_div2 : 256 * q + d = (HDiv.hDiv val P) := Nat.div_add_mod ((HDiv.hDiv val P)) 256
  have h_pow_succ : (HPow.hPow (2 : Nat) (8 * (m + 1))) = P * 256 := by
    have he : 8 * (m + 1) = 8 * m + 8 := Nat.mul_succ 8 m
    rw [he, Nat.pow_add]
  have h_val_decomp : val = (r + d * P) + (P * 256) * q := by
    have h_v1 : val = P * (256 * q + d) + r := by
      have h0 := h_div1.symm
      rw [← h_div2] at h0
      exact h0
    simp only [Nat.left_distrib, Nat.add_comm] at h_v1
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
    exact h_v1
  have h_rhs : (HMod.hMod val (HPow.hPow (2 : Nat) (8 * (m + 1)))) = (HMod.hMod ((r + d * P) + (P * 256) * q) (P * 256)) := by
    rw [h_pow_succ]
    exact congrArg ((fun x => HMod.hMod x (P * 256))) h_val_decomp
  rw [h_rhs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_sum_lt]

private theorem foldl_add_init (xs : List Nat) (g : Nat → Nat) (init : Nat) :
    xs.foldl (fun acc x => acc + g x) init =
      init + xs.foldl (fun acc x => acc + g x) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + g x), ih (g x), Nat.add_assoc]

private theorem endian_digits_fold_mod (endian : Endian) (val n : Nat) :
    (List.range n).foldl (fun acc idx =>
      acc + ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * (if endian == .little then idx else n - idx - 1))))) 256)) *
        (HPow.hPow (2 : Nat) (8 * (if endian == .little then idx else n - idx - 1)))) 0 =
      (HMod.hMod val (HPow.hPow (2 : Nat) (8 * n))) := by
  cases endian with
  | little =>
    simp only [beq_self_eq_true, reduceIte]
    induction n with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      exact digit_step_mod val m
  | big =>
    have h_be : (Endian.big == Endian.little) = false := rfl
    simp only [h_be, Bool.false_eq_true, reduceIte]
    induction n with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hm0 : m + 1 - 0 - 1 = m := by rw [Nat.sub_zero, Nat.add_sub_cancel]
      simp only [Nat.zero_add, hm0]
      have h_fn_eq : (fun acc (x : Nat) =>
          acc + ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * (m + 1 - x.succ - 1))))) 256)) *
            (HPow.hPow (2 : Nat) (8 * (m + 1 - x.succ - 1)))) =
        (fun acc (x : Nat) =>
          acc + ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * (m - x - 1))))) 256)) * (HPow.hPow (2 : Nat) (8 * (m - x - 1)))) := by
        funext acc x
        have hx : m + 1 - x.succ - 1 = m - x - 1 := by rw [Nat.succ_sub_succ_eq_sub]
        rw [hx]
      rw [h_fn_eq, foldl_add_init, ih, Nat.add_comm]
      exact digit_step_mod val m

private theorem readTargetUInt_ofFn_mod (layout : TargetDataLayout) (n val : Nat)
    (limit : n ≤ 16) :
    Mirrors.readTargetUInt layout (Array.ofFn (fun i : Fin n =>
      UInt8.ofNat ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 *
        (if layout.endian == .little then i.1 else n - i.1 - 1))))) 256)))) =
      .ok (BitVec.ofNat 128 ((HMod.hMod val (HPow.hPow (2 : Nat) (8 * n))))) := by
  let arr := Array.ofFn (fun i : Fin n =>
    UInt8.ofNat ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 *
      (if layout.endian == .little then i.1 else n - i.1 - 1))))) 256)))
  have h_sz : arr.size = n := Array.size_ofFn
  rw [readTargetUInt_eq_foldl layout arr (by rw [h_sz]; exact limit)]
  rw [h_sz]
  apply congrArg Except.ok
  apply congrArg (BitVec.ofNat 128)
  have h_congr : ∀ (xs : List Nat) (acc : Nat),
      (∀ idx, idx ∈ xs → idx < n) →
      xs.foldl (fun a idx =>
        a + (arr[idx]?.getD 0).toNat * (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then idx else n - idx - 1)))) acc =
      xs.foldl (fun a idx =>
        a + ((HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * (if layout.endian == .little then idx else n - idx - 1))))) 256)) *
          (HPow.hPow (2 : Nat) (8 * (if layout.endian == .little then idx else n - idx - 1)))) acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < n := h_in idx (List.mem_cons_self)
      have h_ib_arr : idx < arr.size := by rw [h_sz]; exact h_ib
      have h_elem : (arr[idx]?.getD 0).toNat =
          (HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * (if layout.endian == .little then idx else n - idx - 1))))) 256) := by
        rw [Array.getElem?_eq_getElem h_ib_arr, Option.getD_some]
        dsimp only [arr]
        rw [Array.getElem_ofFn]
        have h_lt256 : (HMod.hMod ((HDiv.hDiv val (HPow.hPow (2 : Nat) (8 * (if layout.endian == .little then idx else n - idx - 1))))) 256) < 256 :=
          Nat.mod_lt _ (by decide)
        simp [UInt8.toNat_ofNat']
      simp only [List.foldl_cons, h_elem]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  rw [h_congr (List.range n) 0 (fun idx h => List.mem_range.mp h)]
  exact endian_digits_fold_mod layout.endian val n

/-- If the range is not fully initialized, `getBytesStripProvenance` fails with
`invalidUninitBytes`, reporting the uninitialized sub-range found by the mask.
-/
theorem getBytesStripProvenance_uninit_err [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.getBytesStripProvenance layout range =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  rw [getBytesStripProvenance_eq_R]
  unfold getBytesStripProvenanceR
  simp [h_uninit, bind, Bind.bind, Except.bind, Except.mapError, throw, MonadExceptOf.throw, throwThe]

/--
If the range is initialized and either provenance offsets are addresses or the
range carries no provenance, `getBytesStripProvenance` agrees with
`getBytesUnchecked` on that range (including its bounds/storage errors; this
lemma does not by itself assert success).
-/
theorem getBytesStripProvenance_ok [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.getBytesStripProvenance layout range = allocation.getBytesUnchecked range := by
  rw [getBytesStripProvenance_eq_R, getBytesUnchecked_eq]
  unfold getBytesStripProvenanceR Mirrors.pointerSize
  cases h_prov with
  | inl h_addr =>
    simp [h_init, h_addr, bind, Bind.bind, Except.bind, Except.mapError]
  | inr h_empty =>
    cases Classical.em (PointerProvenance.offsetIsAddr (Prov := P) = true) with
    | inl h_addr =>
      simp [h_init, h_addr, bind, Bind.bind, Except.bind, Except.mapError]
    | inr h_addr =>
      have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_init, h_addr_f, h_empty, bind, Bind.bind, Except.bind, Except.mapError]

/-- If the range is not fully initialized, `readScalar` fails with
`invalidUninitBytes`, reporting the uninitialized sub-range found by the mask.
-/
theorem readScalar_uninit_err [DecidableEq P] [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange) (readProvenance : Bool)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.readScalar layout range readProvenance =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  rw [readScalar_eq_R]
  unfold readScalarR
  simp [h_uninit, bind, Bind.bind, Except.bind, Except.mapError, throw, MonadExceptOf.throw, throwThe]

/--
An integer `readScalar` (without provenance) of an initialized range of at most
16 bytes that is provenance-free (or whose provenance offsets are addresses)
decodes the stored bytes in the target endianness via
`(Scalar.fromUInt … range.size).mapError AllocError.scalar`.
-/
theorem readScalar_int_of_bytes [DecidableEq P] [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bytes : Array UInt8)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (h_limit : bytes.size ≤ 16)
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc idx =>
        acc + (bytes[idx]?.getD 0).toNat * (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then idx else bytes.size - idx - 1)))) 0))
        range.size).mapError AllocError.scalar := by
  rw [readScalar_eq_R]
  unfold readScalarR Mirrors.pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_eq_foldl layout bytes h_limit
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  cases h_prov with
  | inl h_addr =>
    simp [h_addr]
  | inr h_empty =>
    cases Classical.em (PointerProvenance.offsetIsAddr (Prov := P) = true) with
    | inl h_addr =>
      simp [h_addr]
    | inr h_addr =>
      have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_addr_f, h_empty]

/--
Integer round trip: if an initialized, provenance-free (or address-offset) range
of at most 16 bytes holds the target-endian encoding of `bits`, and `bits` fits
in the range, an integer `readScalar` returns
`(Scalar.fromUInt bits range.size).mapError AllocError.scalar`.
-/
theorem readScalar_int_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < (HPow.hPow (2 : Nat) (8 * range.size.bytes.toNat)))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((HMod.hMod ((HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))))) 256))))) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  rw [readScalar_eq_R]
  unfold readScalarR Mirrors.pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  cases h_prov with
  | inl h_addr =>
    simp [h_addr]
  | inr h_empty =>
    cases Classical.em (PointerProvenance.offsetIsAddr (Prov := P) = true) with
    | inl h_addr =>
      simp [h_addr]
    | inr h_addr =>
      have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_addr_f, h_empty]

/-- Pointer round trip: if an initialized pointer-sized range holds the
target-endian encoding of `ptr.offset` and the provenance map reports
`ptr.provenance` at its start, a provenance-reading `readScalar` returns
`Scalar.fromPointer layout ptr`. -/
theorem readScalar_ptr_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (ptr : Pointer P)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_off_bound : ptr.offset.bytes.toNat < (HPow.hPow (2 : Nat) (8 * range.size.bytes.toNat)))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((HMod.hMod ((HDiv.hDiv ptr.offset.bytes.toNat (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))))) 256))))) :
    allocation.readScalar layout range true = .ok (Scalar.fromPointer layout ptr) := by
  rw [readScalar_eq_R]
  unfold readScalarR Mirrors.pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat ptr.offset.bytes.toNat h_limit
  rw [Nat.mod_eq_of_lt h_off_bound] at h_read
  have h_u64_lt := ptr.offset.bytes.toNat_lt
  have h_lt128 : ptr.offset.bytes.toNat < (HPow.hPow (2 : Nat) 128) := Nat.lt_trans h_u64_lt two_pow_64_lt_128
  have h_bv_nat : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt128]
  have h_not_gt : ¬(18446744073709551615 < ptr.offset.bytes.toNat) := Nat.not_lt.mpr (Nat.le_pred_of_lt h_u64_lt)
  have h_ptr_eta : Pointer.new ptr.provenance (Size.ofBytes ptr.offset.bytes) = ptr := by
    cases ptr with
    | mk off prov =>
      cases off with
      | mk b =>
        rfl
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  simp [h_ptr_sz, h_prov, h_bv_nat, h_not_gt, h_ptr_eta]

/--
If an initialized pointer-sized range holds the target-endian encoding of `bits`
and the provenance map reports no provenance at its start, a provenance-reading
`readScalar` returns
`(Scalar.fromUInt bits range.size).mapError AllocError.scalar`.
-/
theorem readScalar_ptr_none_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < (HPow.hPow (2 : Nat) (8 * range.size.bytes.toNat)))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok none)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((HMod.hMod ((HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))))) 256))))) :
    allocation.readScalar layout range true =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  rw [readScalar_eq_R]
  unfold readScalarR Mirrors.pointerSize
  rw [getBytesUnchecked_eq] at h_slice
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  simp [h_ptr_sz, h_prov]

/--
Specification of an in-bounds, nonzero-width (at most 16-byte) `writeScalar` on
a mutable, storage-consistent allocation with a well-formed mask: it succeeds;
preserves size, length, mutability, alignment, extra and native buffer; updates
the mask via `setRange range true` (marking the written range initialized while
preserving other mask bits); installs the specified provenance map; stores the
target-endian encoding of the integer bits or pointer offset; and leaves the
bytes of every disjoint range unchanged.
-/
theorem writeScalar_spec (layout : TargetDataLayout)
    (allocation : Miri.Memory.Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr range.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance) :
    ∃ updated,
      Miri.Memory.Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range true = .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      (∀ b, converted = .bits b →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat ((HMod.hMod ((HDiv.hDiv b.toNat (HPow.hPow (2 : Nat) (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))))) 256))))) ∧
      (∀ p, converted = .pointer p →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat ((HMod.hMod ((HDiv.hDiv (BitVec.ofNat 128 p.offset.bytes.toNat).toNat (HPow.hPow (2 : Nat) (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))))) 256))))) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (range.start.bytes.toNat + range.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ range.start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < (HPow.hPow (2 : Nat) 64) :=
    Nat.lt_of_le_of_lt bound allocation.byteSize.bytes.toNat_lt
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  have h_start_lt_fin : range.start.bytes.toNat < finish.bytes.toNat := by
    rw [finishNat]; exact Nat.lt_add_of_pos_right positive
  let ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint h_start_lt_fin (by rw [maskLength, finishNat]; exact bound)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      h_start_lt_fin (by rw [maskLength, finishNat]; exact bound) maskOk
  let bits : U128 := match converted with
    | .bits b => b
    | .pointer p => BitVec.ofNat 128 p.offset.bytes.toNat
  let data := Array.ofFn (fun i : Fin range.size.bytes.toNat =>
    UInt8.ofNat ((HMod.hMod ((HDiv.hDiv bits.toNat (HPow.hPow (2 : Nat) (8 *
      (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))))) 256)))
  have dataOk : Mirrors.targetUIntBytes layout range.size bits = .ok data :=
    targetUIntBytes_eq_ofFn layout range.size bits width
  have dataSize : data.size = range.size.bytes.toNat := Array.size_ofFn
  let wStart := range.start.bytes.toNat
  let wFin := range.start.bytes.toNat + range.size.bytes.toNat
  let spliced := (raw allocation).extract 0 wStart ++ data ++
    (raw allocation).extract wFin (raw allocation).size
  have h_wFin_raw : wFin ≤ (raw allocation).size := by
    change wFin ≤ allocation.len; rw [storage]; exact bound
  have h_wStart_raw : wStart ≤ (raw allocation).size :=
    Nat.le_trans (Nat.le_add_right _ _) h_wFin_raw
  have bytesLength : spliced.size = allocation.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left h_wStart_raw, Nat.min_self, Nat.sub_zero, dataSize]
    change (wStart + range.size.bytes.toNat) + ((raw allocation).size - wFin) = allocation.byteSize.bytes.toNat
    change (raw allocation).size = allocation.byteSize.bytes.toNat at storage
    exact (Nat.add_sub_of_le h_wFin_raw).trans storage
  have h_clear_raw : allocation.provenanceMap.clear range (raw allocation) (Mirrors.pointerSize layout) =
      .ok () cleared :=
    clear (raw allocation) (getBytesUnchecked_full_rawBytes allocation storage)
  let updated : Miri.Memory.Allocation P E :=
    mkAlloc spliced allocation.byteSize nextProvenance mask allocation.align
      allocation.mutability allocation.extra allocation.nativeBuffer
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  have h_get_data : updated.getBytesUnchecked range = .ok data := by
    rw [getBytesUnchecked_eq]
    have h_fin_ib : finish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat
      rw [finishNat]
      exact bound
    rw [checkedSlice_ok updated range finish h_upd_storage endpoint (Nat.le_of_lt h_start_lt_fin) h_fin_ib]
    rw [finishNat]
    exact congrArg Except.ok
      (splice_extract_exact (raw allocation) data wStart wFin
        (Nat.le_add_right _ _) h_wFin_raw
        (by rw [dataSize]; exact (Nat.add_sub_cancel_left _ _).symm))
  refine ⟨updated, ?_, rfl, bytesLength.trans storage.symm, rfl, rfl, rfl, rfl,
    maskSize, maskWF, maskOk, h_is_init, rfl,
    fun b hb => by subst hb; exact h_get_data,
    fun p hp => by subst hp; exact h_get_data,
    ?_⟩
  · have slice := checkedSlice_ok allocation range finish storage endpoint (Nat.le_of_lt h_start_lt_fin)
      (by rw [finishNat]; exact bound)
    rw [writeScalar_eq_R]
    unfold writeScalarR
    simp only [mutable, bne_self_eq_false, Bool.false_eq_true, reduceIte, conversion,
      Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [slice, maskOk]
    rw [h_clear_raw]
    dsimp only [spliced, wStart, wFin] at bytesLength
    cases converted with
    | bits payload =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength, bne_self_eq_false, Bool.false_eq_true, reduceIte]
      subst insert
      rfl
    | pointer pointer =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength, bne_self_eq_false, Bool.false_eq_true, reduceIte]
      let ⟨sizeEq, inserted⟩ := insert
      have sizeEq' : range.size = Mirrors.pointerSize layout := sizeEq
      have inserted' : cleared.insertPtr range.start pointer.provenance (Mirrors.pointerSize layout) =
          .ok () nextProvenance := inserted
      have h_sz_bne : (range.size != Mirrors.pointerSize layout) = false := by
        rw [sizeEq']
        exact bne_self_eq_false (Mirrors.pointerSize layout)
      simp only [h_sz_bne, Bool.false_eq_true, reduceIte]
      rw [inserted']
      rfl
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq]
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok allocation qRange qFin storage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ (raw allocation).size := by
      change qFin.bytes.toNat ≤ allocation.len; rw [storage]; exact h_qib
    exact congrArg Except.ok
      (splice_extract_disjoint (raw allocation) data wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (Nat.le_add_right _ _) h_wFin_raw h_qlo h_qfin_raw
        (by rw [dataSize]; exact (Nat.add_sub_cancel_left _ _).symm) h_disj)

/-- Writing an empty byte array at an in-bounds offset of a storage-consistent
allocation is the identity. -/
theorem writeBytes_zero_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Miri.Memory.Allocation P E)
    (h_empty : bytes.size = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (inBounds : start.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Miri.Memory.Allocation.writeBytes start bytes ptrSize allocation = .ok () allocation := by
  have h_sfa : Mirrors.sizeForArray 0 = .ok Size.ZERO := rfl
  have h_end : (allocRange start Size.ZERO).endExclusive = .ok start := by
    cases start
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_slice := checkedSlice_ok allocation (allocRange start Size.ZERO) start storage h_end
    (Nat.le_refl _) inBounds
  rw [writeBytes_eq_R]
  unfold writeBytesR
  rw [h_empty, h_sfa]
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, h_slice]
  rfl

/-- Specification of a nonempty in-bounds `writeBytes` on a mutable,
storage-consistent allocation with a well-formed mask: it succeeds; preserves
metadata; updates the mask via `setRange … true` (marking the written range
initialized while preserving other mask bits); installs the specified (cleared)
provenance map; the written range reads back `bytes`; and every disjoint range
is unchanged. -/
theorem writeBytes_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Miri.Memory.Allocation P E) (nextProvenance : ProvenanceMap P)
    (h_nonempty : 0 < bytes.size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : start.bytes.toNat + bytes.size ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) fullBytes ptrSize =
        .ok () nextProvenance) :
    ∃ updated,
      Miri.Memory.Allocation.writeBytes start bytes ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) true =
        .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) =
        .ok bytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (start.bytes.toNat + bytes.size ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have h_u64_alloc := allocation.byteSize.bytes.toNat_lt
  have h_bsz_lt : bytes.size < (HPow.hPow (2 : Nat) 64) :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_of_le_of_lt inBounds h_u64_alloc)
  have h_not_gt_max : ¬(bytes.size > Mirrors.maxU64Nat) := Nat.not_lt.mpr (le_maxU64Nat_of_lt h_bsz_lt)
  let writeSize := Size.ofBytes (UInt64.ofNat bytes.size)
  have h_wsz_nat : writeSize.bytes.toNat = bytes.size := by
    simp [writeSize, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_bsz_lt]
  have h_sfa : Mirrors.sizeForArray bytes.size = .ok writeSize := by
    unfold Mirrors.sizeForArray
    simp [h_not_gt_max, h_wsz_nat, writeSize, pure, Pure.pure, Except.pure]
  have h_wsz_nz : (writeSize.bytes == 0) = false := by
    apply beq_false_of_ne
    intro h0
    have h0' : writeSize.bytes.toNat = 0 := by simp [h0]
    rw [h_wsz_nat] at h0'
    exact Nat.ne_of_gt h_nonempty h0'
  let range := allocRange start writeSize
  have fits : start.bytes.toNat + writeSize.bytes.toNat < (HPow.hPow (2 : Nat) 64) := by
    rw [h_wsz_nat]; exact Nat.lt_of_le_of_lt inBounds h_u64_alloc
  let finish := Size.ofBytes (start.bytes + writeSize.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end range allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size start writeSize fits)
  have finishNat : finish.bytes.toNat = start.bytes.toNat + bytes.size := by
    have h_def : finish.bytes.toNat = (start.bytes + writeSize.bytes).toNat := rfl
    rw [h_def, UInt64.toNat_add, Nat.mod_eq_of_lt fits, h_wsz_nat]
  have h_lt_fin : start.bytes.toNat < finish.bytes.toNat := by
    rw [finishNat]; exact Nat.lt_add_of_pos_right h_nonempty
  have h_fin_le_bs : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat := by
    rw [finishNat]; exact inBounds
  let ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint h_lt_fin (by rw [maskLength]; exact h_fin_le_bs)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      h_lt_fin (by rw [maskLength]; exact h_fin_le_bs) maskOk
  have h_slice := checkedSlice_ok allocation range finish storage endpoint
    (Nat.le_of_lt h_lt_fin) h_fin_le_bs
  have h_clear_raw : allocation.provenanceMap.clear range (raw allocation) ptrSize =
      .ok () nextProvenance :=
    clear (raw allocation) (getBytesUnchecked_full_rawBytes allocation storage)
  let wStart := start.bytes.toNat
  let wFin := finish.bytes.toNat
  let spliced := (raw allocation).extract 0 wStart ++ bytes ++
    (raw allocation).extract wFin (raw allocation).size
  have h_wFin_raw : wFin ≤ (raw allocation).size := by
    change wFin ≤ allocation.len; rw [storage]; exact h_fin_le_bs
  have h_wStart_raw : wStart ≤ (raw allocation).size :=
    Nat.le_trans (Nat.le_of_lt h_lt_fin) h_wFin_raw
  have bytesLength : spliced.size = allocation.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left h_wStart_raw, Nat.min_self, Nat.sub_zero]
    change (wStart + bytes.size) + ((raw allocation).size - wFin) = allocation.byteSize.bytes.toNat
    change (raw allocation).size = allocation.byteSize.bytes.toNat at storage
    have h_wf_eq : wFin = wStart + bytes.size := finishNat
    rw [← h_wf_eq, Nat.add_sub_of_le h_wFin_raw, storage]
  let updated : Miri.Memory.Allocation P E :=
    mkAlloc spliced allocation.byteSize nextProvenance mask allocation.align
      allocation.mutability allocation.extra allocation.nativeBuffer
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  refine ⟨updated, ?_, rfl, bytesLength.trans storage.symm, rfl, rfl, rfl, rfl,
    maskSize, maskWF, maskOk, h_is_init, rfl, ?_, ?_⟩
  · dsimp only [range] at maskOk h_clear_raw endpoint h_slice
    rw [writeBytes_eq_R]
    unfold writeBytesR setInitialization overwriteRawBytes
    rw [h_sfa]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    change (match checkedSlice allocation (allocRange start writeSize) with
      | .error reason => EStateM.Result.error reason allocation
      | .ok _ => _) = _
    rw [h_slice]
    simp only [h_wsz_nz, Bool.false_eq_true, reduceIte, mutable, bne_self_eq_false,
      maskOk, Except.mapError, Except.bind, Except.pure, raw_withInitMask, provenanceMap_withInitMask]
    rw [h_clear_raw]
    dsimp only
    rw [endpoint]
    dsimp only [Except.mapError, Except.bind, allocRange]
    have h_len_chk : (spliced.size != allocation.byteSize.bytes.toNat) = false := by
      change (spliced.size != allocation.byteSize.bytes.toNat) = false
      rw [bytesLength]
      exact bne_self_eq_false _
    dsimp only [spliced, wStart, wFin, allocRange] at h_len_chk
    simp only [raw_withProvenance, raw_withInitMask, byteSize_withProvenance, byteSize_withInitMask]
    simp only [h_len_chk, Bool.false_eq_true, reduceIte]
    rfl
  · rw [getBytesUnchecked_eq]
    have h_fin_ib : finish.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_fin_le_bs
    rw [checkedSlice_ok updated range finish h_upd_storage endpoint
      (Nat.le_of_lt h_lt_fin) h_fin_ib]
    exact congrArg Except.ok
      (splice_extract_exact (raw allocation) bytes wStart wFin
        (Nat.le_of_lt h_lt_fin) h_wFin_raw
        (by dsimp only [wStart, wFin]; rw [finishNat]; exact (Nat.add_sub_cancel_left _ _).symm))
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq]
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok allocation qRange qFin storage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ (raw allocation).size := by
      change qFin.bytes.toNat ≤ allocation.len; rw [storage]; exact h_qib
    exact congrArg Except.ok
      (splice_extract_disjoint (raw allocation) bytes wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (Nat.le_of_lt h_lt_fin) h_wFin_raw h_qlo h_qfin_raw
        (by dsimp only [wStart, wFin]; rw [finishNat]; exact (Nat.add_sub_cancel_left _ _).symm)
        (by dsimp only [wStart, wFin]; rw [finishNat]; exact h_disj))

/--
`writeUninit` of an empty in-bounds range of a storage-consistent allocation is
the identity.
-/
theorem writeUninit_zero_spec (range : AllocRange) (finish ptrSize : Size)
    (allocation : Miri.Memory.Allocation P E)
    (h_zero : range.size.bytes = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Miri.Memory.Allocation.writeUninit range ptrSize allocation = .ok () allocation := by
  have h_slice := checkedSlice_ok allocation range finish storage endEq startLe inBounds
  rw [writeUninit_eq_R]
  unfold writeUninitR
  simp [h_slice, h_zero, Id.run, pure, Pure.pure]

/-- Specification of a nonempty in-bounds `writeUninit` on a mutable,
storage-consistent allocation with a well-formed mask: it succeeds; preserves
metadata; marks the range uninitialized (`setRange range false`); installs the
specified (cleared) provenance map; and leaves every byte unchanged. -/
theorem writeUninit_spec (range : AllocRange) (ptrSize : Size)
    (allocation : Miri.Memory.Allocation P E) (nextProvenance : ProvenanceMap P)
    (nonzero : range.size.bytes ≠ 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes ptrSize = .ok () nextProvenance) :
    ∃ updated,
      Miri.Memory.Allocation.writeUninit range ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range false = .ok updated.initializationMask ∧
      updated.provenanceMap = nextProvenance ∧
      ∀ (anyRange : AllocRange),
        updated.getBytesUnchecked anyRange = allocation.getBytesUnchecked anyRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < (HPow.hPow (2 : Nat) 64) :=
    Nat.lt_of_le_of_lt inBounds allocation.byteSize.bytes.toNat_lt
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  have h_lt_fin : range.start.bytes.toNat < finish.bytes.toNat := by
    rw [finishNat]; exact Nat.lt_add_of_pos_right positive
  let ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish false
      maskValid endpoint h_lt_fin (by rw [maskLength, finishNat]; exact inBounds)
  have h_slice := checkedSlice_ok allocation range finish storage endpoint
    (Nat.le_of_lt h_lt_fin) (by rw [finishNat]; exact inBounds)
  have h_clear_raw : allocation.provenanceMap.clear range (raw allocation) ptrSize =
      .ok () nextProvenance :=
    clear (raw allocation) (getBytesUnchecked_full_rawBytes allocation storage)
  let updated : Miri.Memory.Allocation P E :=
    mkAlloc (raw allocation) allocation.byteSize nextProvenance mask allocation.align
      allocation.mutability allocation.extra allocation.nativeBuffer
  refine ⟨updated, ?_, rfl, rfl, rfl, rfl, rfl, rfl, maskSize, maskWF, maskOk, rfl, fun _ => rfl⟩
  have h_nz_beq : (range.size.bytes == 0) = false := beq_false_of_ne nonzero
  rw [writeUninit_eq_R]
  unfold writeUninitR setInitialization
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, h_slice, h_nz_beq,
    Bool.false_eq_true, reduceIte, mutable, bne_self_eq_false,
    maskOk, Except.mapError, Except.bind, Except.pure, raw_withInitMask, provenanceMap_withInitMask]
  rw [h_clear_raw]
  rfl

-- Excluded under Option C (#4009): `Allocation.copyRepeatedly_initialized_spec`
-- and `Allocation.copy_initialized_spec` depend on
-- `InitMask.WriteProof.prepareCopy_of_uniform` (blocked on
-- `_private...InitMask.collectChunksAux` reducibility in unmodified
-- `vendor/lean-miri/Miri/Memory/InitMask.lean`). Deferred to a follow-up PR.

end Allocation


/-! ## Part 4. Top-level `Anneal.MirCorrespondence.MemoryLemmas` re-exports -/

export InitMask.WriteProof (get_ok_of_wellFormed set_range_get
  isRangeInitialized_nonempty_iff isRangeInitialized_after_setRange_true isRangeInitialized_frame
  applyCopy_singleton)

export ProvenanceMap (rangeEmpty_new readPtr_new prepareCopy_new applyCopy_empty)

export Allocation (byteSize_withExtra len_withExtra align_withExtra
  mutability_withExtra provenanceMap_withExtra initializationMask_withExtra
  getBytesUnchecked_withExtra byteSize_mapExtra len_mapExtra align_mapExtra mutability_mapExtra
  provenanceMap_mapExtra initializationMask_mapExtra getBytesUnchecked_mapExtra
  getBytesStripProvenance_mapExtra readScalar_mapExtra writeBytes_mapExtra clearProvenance_mapExtra
  fromBytes_spec fromBytes_exists tryNew_spec tryNew_exists getBytesUnchecked_size
  getBytesUnchecked_subrange getBytesUnchecked_split getBytesStripProvenance_uninit_err
  getBytesStripProvenance_ok readScalar_uninit_err readScalar_int_of_bytes readScalar_int_roundtrip
  readScalar_ptr_roundtrip readScalar_ptr_none_roundtrip writeScalar_spec writeBytes_zero_spec
  writeBytes_spec writeUninit_zero_spec writeUninit_spec)

/-! ## Part 5. Non-vacuity witnesses (47 / 50 `#4022` theorems)

Compile-time checks that the hypotheses of all 47 ported specification theorems
are jointly satisfiable on concrete states, by instantiating every theorem in
closed or existentially-constructed `private theorem`s (unlike `example`,
`private theorem` declarations remain in `env.constants` so `anneal-audit`
replays and audits their axiom footprint while adding zero public
API). They cover multi-block `.Lazy` → `.Materialized` `InitMask` transitions
(`64` and `128` byte boundaries), `ProvenanceMap` operations, `fromBytes` /
`tryNew` (`.Uninit` and `.Zero`), framed `writeBytes`, `writeUninit`,
zero-length writes, `getBytesUnchecked` size/subrange/split,
`getBytesStripProvenance` (both `CtfeProvenance` empty-range and `Provenance`
`offsetIsAddr = true` live-pointer stripping), little- and big-endian integer
and pointer `writeScalar` / `readScalar` roundtrips and pointer-to-integer
transmutation, `withExtra` / `mapExtra` commutations,
`ProvenanceMap.prepareCopy_new` / `applyCopy_empty`, and concrete 64-bit
`InitMask` word layouts paired with `.Materialized` `set_range_get` /
`isRangeInitialized_frame` proofs (`copy` / `copyRepeatedly` /
`prepareCopy_of_uniform` are excluded under Option C). -/

namespace NonVacuity
open Miri.ABI Miri.Memory

/--
1. All 6 Pass-1 `InitMask.WriteProof` theorems across two 64-bit word boundaries
(`64` and `128`), starting from a `.Lazy false` mask.
-/
private theorem wit_initMask_full_chain :
    ∃ (u uCopy : InitMask) (b0 : Bool) (bad : AllocRange),
      (InitMask.new (Size.ofBytes 200) false).get Size.ZERO = .ok b0 ∧
      (InitMask.new (Size.ofBytes 200) false).setRange
        (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok u ∧
      u.get (Size.ofBytes 59) = .ok false ∧ u.get (Size.ofBytes 60) = .ok true ∧
      u.get (Size.ofBytes 63) = .ok true ∧ u.get (Size.ofBytes 64) = .ok true ∧
      u.get (Size.ofBytes 127) = .ok true ∧ u.get (Size.ofBytes 128) = .ok true ∧
      u.get (Size.ofBytes 139) = .ok true ∧ u.get (Size.ofBytes 140) = .ok false ∧
      u.isRangeInitialized (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok (.ok ()) ∧
      (u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ()) ↔
        (InitMask.new (Size.ofBytes 200) false).isRangeInitialized
          (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ())) ∧
      u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.error bad) ∧
      u.applyCopy ⟨true, [80].toArray⟩ (allocRange Size.ZERO (Size.ofBytes 80)) 2 = .ok uCopy := by
  let m0 := InitMask.new (Size.ofBytes 200) false
  have hwf0 : InitMask.WriteProof.WellFormed m0 := True.intro
  let ⟨b0, hb0⟩ := InitMask.WriteProof.get_ok_of_wellFormed m0 Size.ZERO hwf0 (by decide)
  have hend : (allocRange (Size.ofBytes 60) (Size.ofBytes 80)).endExclusive =
      .ok (Size.ofBytes 140) := by decide
  let ⟨u, hu, hlen, hwfu⟩ := InitMask.WriteProof.set_range_exists m0
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwf0 hend
    (by decide) (by decide)
  have hget : ∀ idx : Size, idx.bytes.toNat < 200 → u.get idx =
      if 60 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 140 then .ok true else .ok false :=
    fun idx hidx => InitMask.WriteProof.set_range_get m0 u
      (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) idx true hwf0 hend
      (by decide) (by decide) hidx hu
  have his := InitMask.WriteProof.isRangeInitialized_after_setRange_true m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) hwf0 hend
    (by decide) (by decide) hu
  have hfr := InitMask.WriteProof.isRangeInitialized_frame m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (allocRange Size.ZERO (Size.ofBytes 60))
    (Size.ofBytes 140) (Size.ofBytes 60) true hwf0 hend (by decide)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) hu
  have h59 : u.get (Size.ofBytes 59) = .ok false := by rw [hget _ (by decide)]; decide
  let ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff u
    (allocRange Size.ZERO (Size.ofBytes 60)) (Size.ofBytes 60) hwfu (by decide)
    (by decide) (by rw [hlen]; decide)).2 ⟨Size.ofBytes 59, by decide, by decide, h59⟩
  have hap := InitMask.WriteProof.applyCopy_singleton u Size.ZERO (Size.ofBytes 80)
    (Size.ofBytes 160) 2 true (by decide) (by decide)
  let ⟨uCopy, huCopy, _, _⟩ := InitMask.WriteProof.set_range_exists u
    (allocRange Size.ZERO (Size.ofBytes 160)) (Size.ofBytes 160) true hwfu (by decide)
    (by decide) (by rw [hlen]; decide)
  refine ⟨u, uCopy, b0, bad, hb0, hu, h59, ?_, ?_, ?_, ?_, ?_, ?_, ?_, his, hfr, hbad,
    hap.trans huCopy⟩ <;> rw [hget _ (by decide)] <;> decide

/-- 2. `fromBytes_exists` / `fromBytes_spec`, `writeBytes_spec`,
`writeBytes_zero_spec`, `getBytesUnchecked_{size,subrange,split}`, and all 18
`withExtra`/`mapExtra` lemmas. -/
private theorem wit_fromBytes_writeBytes_slices_and_mapExtra :
    ∃ (alloc updated : Allocation CtfeProvenance Unit) (slice26 : Array UInt8),
      Allocation.fromBytes (Array.replicate 8 (0 : UInt8)) Align.ONE .Mut = .ok alloc ∧
      Allocation.writeBytes (Size.ofBytes 8) List.nil.toArray (Size.ofBytes 8) alloc = .ok () alloc ∧
      Allocation.writeBytes (Size.ofBytes 2) [7, 9].toArray (Size.ofBytes 8) alloc = .ok () updated ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok [7, 9].toArray ∧
      updated.initializationMask.isRangeInitialized
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok (.ok ()) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) = .ok [0, 0, 0, 0].toArray ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) = .ok slice26 ∧
      slice26.size = 4 ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 3) (Size.ofBytes 2)) =
        .ok (slice26.extract 1 3) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) =
        .ok ([7, 9].toArray ++ [0, 0, 0, 0].toArray) ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).byteSize = updated.byteSize ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).len = updated.len ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).align = updated.align ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).mutability = updated.mutability ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).provenanceMap = updated.provenanceMap ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).initializationMask =
        updated.initializationMask ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).getBytesUnchecked
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).getBytesStripProvenance ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesStripProvenance ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).readScalar ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false =
        updated.readScalar ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false ∧
      Allocation.writeBytes (Size.ofBytes 2) [7, 9].toArray (Size.ofBytes 8) (alloc.mapExtra id) =
        .ok () (updated.mapExtra id) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
        (updated.mapExtra id) =
        (match Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
            (Size.ofBytes 8) updated with
         | .ok v s => .ok v (s.mapExtra id)
         | .error e s => .error e (s.mapExtra id)) := by
  let ⟨alloc, hcreated, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    (Array.replicate 8 0) Align.ONE 1 .Mut rfl rfl (by decide)
  let ⟨hbs, hlen, hmut, _, _, hprov, hmask, hwf, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hzero := Allocation.writeBytes_zero_spec (Size.ofBytes 8) (Size.ofBytes 8) List.nil.toArray alloc
    rfl (hlen.trans hbs.symm) (by rw [hbs]; decide)
  let ⟨updated, hw, hbsU, hlenU, _, _, _, _, _, _, _, hinit, _, hget22, hframe⟩ :=
    Allocation.writeBytes_spec (Size.ofBytes 2) (Size.ofBytes 8) [7, 9].toArray alloc ProvenanceMap.new
      (by decide) (hlen.trans hbs.symm) hmut (by rw [hmask]; rfl) hwf (by rw [hbs]; decide)
      (fun _ _ => by
        rw [hprov]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
  have hget44 : updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) =
      .ok [0, 0, 0, 0].toArray := by
    rw [hframe _ (Size.ofBytes 8) (by decide) (by decide) (by rw [hbs]; decide) (by decide),
      hslice _ (Size.ofBytes 8) (by decide) (by decide) (by decide)]
    decide
  have hstorU : updated.len = updated.byteSize.bytes.toNat :=
    hlenU.trans (hlen.trans (hbs.symm.trans (congrArg (·.bytes.toNat) hbsU.symm)))
  let ⟨slice26, hget24, hsz24⟩ := Allocation.getBytesUnchecked_size updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (Size.ofBytes 6) hstorU
    (by decide) (by decide) (by rw [hbsU, hbs]; decide)
  have hsub := Allocation.getBytesUnchecked_subrange updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (allocRange (Size.ofBytes 3) (Size.ofBytes 2))
    (Size.ofBytes 6) (Size.ofBytes 5) slice26 (by decide) (by decide)
    (by decide) (by decide) (by decide) hget24
  have hsplit := Allocation.getBytesUnchecked_split updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) (allocRange (Size.ofBytes 4) (Size.ofBytes 4))
    (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) (Size.ofBytes 4) (Size.ofBytes 8)
    [7, 9].toArray [0, 0, 0, 0].toArray (by decide) rfl (by decide) rfl (by decide)
    (by decide) (by decide) hget22 hget44
  have hw_map := Allocation.writeBytes_mapExtra (Size.ofBytes 2) [7, 9].toArray (Size.ofBytes 8) alloc id
  rw [hw] at hw_map
  refine ⟨alloc, updated, slice26, hcreated, hzero, hw, hget22, hinit, hget44, hget24,
    hsz24, hsub, hsplit,
    (Allocation.byteSize_mapExtra _ _).trans (Allocation.byteSize_withExtra _ _),
    (Allocation.len_mapExtra _ _).trans (Allocation.len_withExtra _ _),
    (Allocation.align_mapExtra _ _).trans (Allocation.align_withExtra _ _),
    (Allocation.mutability_mapExtra _ _).trans (Allocation.mutability_withExtra _ _),
    (Allocation.provenanceMap_mapExtra _ _).trans (Allocation.provenanceMap_withExtra _ _),
    (Allocation.initializationMask_mapExtra _ _).trans (Allocation.initializationMask_withExtra _ _),
    (Allocation.getBytesUnchecked_mapExtra _ _ _).trans
      (Allocation.getBytesUnchecked_withExtra _ _ _),
    Allocation.getBytesStripProvenance_mapExtra _ _ _ _,
    Allocation.readScalar_mapExtra _ _ _ _ _,
    hw_map, ?_⟩
  rw [Allocation.clearProvenance_mapExtra]
  cases Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
    (Size.ofBytes 8) updated <;> rfl

/-- 3. `tryNew_exists` / `tryNew_spec` (both `.Uninit` and `.Zero`),
`getBytesStripProvenance_{uninit_err,ok}`, `readScalar_uninit_err`, and
`writeUninit_{zero_,}spec`. -/
private theorem wit_tryNew_strip_and_writeUninit :
    ∃ (aUninit aZero aDeinit : Allocation CtfeProvenance Unit) (bad : AllocRange),
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aUninit ∧
      aUninit.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      aUninit.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) false =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Zero
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aZero ∧
      aZero.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .ok [0, 0, 0, 0].toArray ∧
      Allocation.writeUninit (allocRange (Size.ofBytes 8) Size.ZERO) (Size.ofBytes 8) aZero =
        .ok () aZero ∧
      Allocation.writeUninit (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8) aZero =
        .ok () aDeinit ∧
      aDeinit.initializationMask.get Size.ZERO = .ok false ∧
      aDeinit.initializationMask.get (Size.ofBytes 2) = .ok true ∧
      aDeinit.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok [0, 0, 0, 0].toArray := by
  let ⟨aUninit, huNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨hbsU, _, _, _, _, _, hmaskU, _, hwfU, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit aUninit huNew
  have hmU := hmaskU rfl
  have hget0_false : aUninit.initializationMask.get Size.ZERO = .ok false := by rw [hmU]; rfl
  let ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff
    aUninit.initializationMask (allocRange Size.ZERO (Size.ofBytes 4)) (Size.ofBytes 4)
    hwfU (by decide) (by decide) (by rw [hmU]; decide)).2
    ⟨Size.ZERO, by decide, by decide, hget0_false⟩
  have hstripErr := Allocation.getBytesStripProvenance_uninit_err aUninit ⟨.little, .w64⟩ _ bad hbad
  have hreadErr := Allocation.readScalar_uninit_err aUninit ⟨.little, .w64⟩ _ bad false hbad
  let ⟨aZero, hzNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Zero (by decide) (by decide)
  let ⟨hbsZ, hlenZ, hmutZ, _, _, hprovZ, _, hmaskZ, hwfZ, hsliceZ⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Zero aZero hzNew
  have hmZ := hmaskZ rfl
  have hend4 : (allocRange Size.ZERO (Size.ofBytes 4)).endExclusive = .ok (Size.ofBytes 4) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  have hinitZ : aZero.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok (.ok ()) := by
    rw [hmZ]
    exact InitMask.lazy_initialized_query _ _ _ hend4 (by decide)
  have hstripOk : aZero.getBytesStripProvenance ⟨.little, .w64⟩
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok [0, 0, 0, 0].toArray := by
    rw [Allocation.getBytesStripProvenance_ok aZero _ _ hinitZ
      (Or.inr (by rw [hprovZ]; exact Anneal.MirCorrespondence.MemoryLemmas.ProvenanceMap.rangeEmpty_new _ _ _ hps hend4))]
    exact hsliceZ _ _ hend4 (by decide) (by decide)
  have hstorZ : aZero.len = aZero.byteSize.bytes.toNat := by rw [hlenZ, hbsZ]
  have hwuZero := Allocation.writeUninit_zero_spec (allocRange (Size.ofBytes 8) Size.ZERO)
    (Size.ofBytes 8) (Size.ofBytes 8) aZero rfl hstorZ (by decide) (by decide)
    (by rw [hbsZ]; decide)
  let ⟨aDeinit, hwu, _, _, _, _, _, _, _, _, hsetF, _, hbytesEq⟩ :=
    Allocation.writeUninit_spec (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
      aZero ProvenanceMap.new (by decide) hstorZ hmutZ (by rw [hmZ, hbsZ]; rfl) hwfZ
      (by rw [hbsZ]; decide)
      (fun _ _ => by
        rw [hprovZ]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 2) (by decide) (by decide))
  have hg0 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    Size.ZERO false hwfZ (by decide) (by decide) (by rw [hmZ]; decide) (by rw [hmZ]; decide) hsetF
  have hg2 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    (Size.ofBytes 2) false hwfZ (by decide) (by decide) (by rw [hmZ]; decide)
    (by rw [hmZ]; decide) hsetF
  have hmZ0 : aZero.initializationMask.get Size.ZERO = .ok true := by rw [hmZ]; rfl
  have hmZ2 : aZero.initializationMask.get (Size.ofBytes 2) = .ok true := by rw [hmZ]; rfl
  refine ⟨aUninit, aZero, aDeinit, bad, huNew, hstripErr, hreadErr, hzNew, hstripOk, hwuZero,
    hwu, ?_, ?_, (hbytesEq _).trans (hsliceZ _ _ hend4 (by decide) (by decide))⟩
  · rw [hg0, hmZ0]; decide
  · rw [hg2, hmZ2]; decide

/-- 4. `readScalar_int_of_bytes` decodes `#[1, 2]` as `0x0201` on little-endian
targets and `0x0102` on big-endian targets. -/
private theorem wit_readScalar_int_of_bytes (endian : Endian) :
    ∃ alloc : Allocation CtfeProvenance Unit,
      Allocation.fromBytes [1, 2].toArray Align.ONE .Not = .ok alloc ∧
      alloc.readScalar ⟨endian, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 2)) false =
        (Scalar.fromUInt (BitVec.ofNat 128 (if endian == .little then 0x0201 else 0x0102))
          (Size.ofBytes 2)).mapError AllocError.scalar := by
  let ⟨alloc, hcreated, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    [1, 2].toArray Align.ONE 1 .Not rfl rfl (by decide)
  let ⟨hbs, _, _, _, _, hprov, hmask, _, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hend : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  refine ⟨alloc, hcreated, ?_⟩
  rw [Allocation.readScalar_int_of_bytes alloc _ _ [1, 2].toArray
    (by
      rw [hmask]
      exact InitMask.lazy_initialized_query _ _ _ hend
        (UInt64.le_iff_toNat_le.mpr (by rw [hbs]; decide)))
    (hslice _ _ hend (by decide) (by decide)) (by decide)
    (Or.inr (by rw [hprov]; exact Anneal.MirCorrespondence.MemoryLemmas.ProvenanceMap.rangeEmpty_new _ _ _ hps hend))]
  cases endian <;> rfl

/-- 5. `writeScalar_spec` (both `.bits` and `.pointer` branches) chained into
`readScalar_int_roundtrip`, `readScalar_ptr_none_roundtrip`, and
`readScalar_ptr_roundtrip` across both little- and big-endian target layouts. -/
private theorem wit_writeScalar_and_readScalar_roundtrips (endian : Endian) :
    ∃ (a0 aBits : Allocation CtfeProvenance Unit) (p0 pPtr : Allocation Provenance Unit),
      let layout : TargetDataLayout := ⟨endian, .w64⟩
      let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
      let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
      let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok a0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) intVal a0 =
        .ok () aBits ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) false = .ok intVal ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok intVal ∧
      Allocation.tryNew (Size.ofBytes 16) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok p0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) ptrVal p0 =
        .ok () pPtr ∧
      pPtr.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok ptrVal ∧
      pPtr.getBytesUnchecked (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) =
        .ok (Array.replicate 8 0) := by
  let layout : TargetDataLayout := ⟨endian, .w64⟩
  let bits : U128 := BitVec.ofNat 128 (0x0102030405060708 : UInt64).toNat
  let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
  let r08 := allocRange Size.ZERO (Size.ofBytes 8)
  have hend08 : r08.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hps_eq : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by
    dsimp only [layout]; decide
  have hps_nz : (Size.fromBits layout.pointerWidth.bits).bytes ≠ 0 := by
    dsimp only [layout]; decide
  let ⟨a0, ha0, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨hbs0, hlen0, hmut0, _, _, hprov0, hmask0, _, hwf0, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit a0 ha0
  let ⟨aBits, hwBits, _, _, _, _, _, _, _, _, _, hisBits, hprovBits, hbytesBits, _, _⟩ :=
    Allocation.writeScalar_spec layout a0 r08 intVal (.bits bits) ProvenanceMap.new ProvenanceMap.new
      (by rw [hlen0, hbs0]) hmut0 (by rw [hmask0 rfl, hbs0]; rfl) hwf0
      (by decide) (by decide) (by rw [hbs0]; decide) (by decide)
      (fun _ _ => by
        rw [hprov0, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      rfl
  have hfromUInt : (Scalar.fromUInt (Prov := CtfeProvenance) bits r08.size).mapError
      AllocError.scalar = .ok intVal := by decide
  have hreadInt := Allocation.readScalar_int_roundtrip aBits layout r08 bits
    hisBits (by decide) (by decide)
    (Or.inr (by rw [hprovBits]; exact Anneal.MirCorrespondence.MemoryLemmas.ProvenanceMap.rangeEmpty_new _ _ _ hps_nz hend08))
    (hbytesBits bits rfl)
  have hreadPtrNone := Allocation.readScalar_ptr_none_roundtrip aBits layout r08 bits
    hisBits hps_eq.symm (by decide) (by decide)
    (by rw [hprovBits, hps_eq]; exact Anneal.MirCorrespondence.MemoryLemmas.ProvenanceMap.readPtr_new _ _ _ (by decide) hend08)
    (hbytesBits bits rfl)
  let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
  let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
  let ⟨pm1, hpm1_ins, hpm1_ptrs⟩ :
      ∃ pm1 : ProvenanceMap Provenance,
        ProvenanceMap.insertPtr Size.ZERO Provenance.wildcard (Size.ofBytes 8) ProvenanceMap.new =
          .ok () pm1 ∧
        pm1.ptrs = [(Size.ZERO, Provenance.wildcard)].toArray :=
    ⟨_, ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      Provenance.wildcard (by decide) hend08, rfl⟩
  have hconvPtr : ptrVal.toBitsOrPtrInternal r08.size = .ok (.pointer ptr) := by
    cases endian <;> decide
  let ⟨p0, hp0, _⟩ := Allocation.tryNew_exists (P := Provenance)
    (Size.ofBytes 16) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨hbsP, hlenP, hmutP, _, _, hprovP, hmaskP, _, hwfP, hsliceP⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 16) Align.EIGHT .Uninit p0 hp0
  let ⟨pPtr, hwPtr, _, _, _, _, _, _, _, _, _, hisPtr, hprovPtr, _, hbytesPtr, hframePtr⟩ :=
    Allocation.writeScalar_spec layout p0 r08 ptrVal (.pointer ptr) ProvenanceMap.new pm1
      (by rw [hlenP, hbsP]) hmutP (by rw [hmaskP rfl, hbsP]; rfl) hwfP
      (by decide) (by decide) (by rw [hbsP]; decide) hconvPtr
      (fun _ _ => by
        rw [hprovP, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      ⟨hps_eq.symm, by rw [hps_eq]; exact hpm1_ins⟩
  have hpSlice : pPtr.getBytesUnchecked r08 =
      .ok (Array.ofFn (fun i : Fin r08.size.bytes.toNat =>
        UInt8.ofNat ((HMod.hMod ((HDiv.hDiv ptr.offset.bytes.toNat (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then i.1 else r08.size.bytes.toNat - i.1 - 1))))) 256)))) := by
    have hbv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by decide
    have _h_simpa := hbytesPtr ptr rfl
    simp [hbv] at _h_simpa
    simp
    exact _h_simpa
  have hgetPtr : pm1.getPtr r08.start = some ptr.provenance := by
    unfold ProvenanceMap.getPtr
    rw [hpm1_ptrs]
    decide
  have hreadPtr := Allocation.readScalar_ptr_roundtrip pPtr layout r08 ptr
    hisPtr hps_eq.symm (by decide) (by decide)
    (by rw [hprovPtr, hps_eq]; exact ProvenanceMap.read_exact_pointer pm1 _ _ _ hgetPtr) hpSlice
  have hfr8 := hframePtr (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by rw [hbsP]; decide) (Or.inl (by decide))
  have hp8 := hsliceP (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by decide)
  exact ⟨a0, aBits, p0, pPtr, ha0, hwBits, hreadInt.trans hfromUInt,
    hreadPtrNone.trans hfromUInt, hp0, hwPtr, hreadPtr, hfr8.trans hp8⟩

/--
6. `ProvenanceMap.prepareCopy_new` and `ProvenanceMap.applyCopy_empty` (note:
`copy_initialized_spec` and `copyRepeatedly_initialized_spec` are excluded under
Option C pending a `collectChunksAux` follow-up PR).
-/
private theorem wit_provenanceMap_prepareCopy_applyCopy :
    (Miri.Memory.ProvenanceMap.new : Miri.Memory.ProvenanceMap CtfeProvenance).prepareCopy
        (allocRange Size.ZERO (Size.ofBytes 2)) [5, 6].toArray (Size.ofBytes 8) =
      .ok ⟨List.nil.toArray, List.nil.toArray⟩ ∧
    Miri.Memory.ProvenanceMap.applyCopy
        ⟨List.nil.toArray, List.nil.toArray⟩ (allocRange Size.ZERO (Size.ofBytes 2)) 3
        (Miri.Memory.ProvenanceMap.new : Miri.Memory.ProvenanceMap CtfeProvenance) =
      .ok () (Miri.Memory.ProvenanceMap.new : Miri.Memory.ProvenanceMap CtfeProvenance) :=
  ⟨Anneal.MirCorrespondence.MemoryLemmas.ProvenanceMap.prepareCopy_new
      (allocRange Size.ZERO (Size.ofBytes 2)) [5, 6].toArray (Size.ofBytes 8) (Size.ofBytes 2)
      (by decide) (by decide),
    Anneal.MirCorrespondence.MemoryLemmas.ProvenanceMap.applyCopy_empty _ _ _⟩


/-- 7. Concrete 64-bit word layouts, checked over `Mirrors` via `decide` (zero
`Lean.ofReduceBool`), paired with `.Materialized`-input instantiations of
`set_range_get` (`.Materialized` → `.Materialized` clearing write straddling
byte 64 and `.Materialized` → `.Lazy` full overwrite),
`isRangeInitialized_frame` (`state = false`, `Or.inl` disjoint branch on
`.Materialized`), and `get_ok_of_wellFormed` on `.Materialized`. -/
private theorem wit_initMask_word_layout :
    let m1 : InitMask :=
      ⟨.Materialized ⟨[0xF000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFF, 0].toArray⟩, Size.ofBytes 200⟩
    let m2 : InitMask :=
      ⟨.Materialized ⟨[0x3000000000000000, 0xFFFFFFFFFFFFFFFC, 0xFFF, 0].toArray⟩, Size.ofBytes 200⟩
    (InitMask.new (Size.ofBytes 200) false).setRange
        (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok m1 ∧
    m1.setRange (allocRange (Size.ofBytes 62) (Size.ofBytes 4)) false = .ok m2 ∧
    m2.setRange (allocRange Size.ZERO (Size.ofBytes 200)) true =
      .ok (InitMask.new (Size.ofBytes 200) true) ∧
    m2.get (Size.ofBytes 61) = .ok true ∧
    m2.get (Size.ofBytes 62) = .ok false ∧
    m2.get (Size.ofBytes 65) = .ok false ∧
    m2.get (Size.ofBytes 66) = .ok true ∧
    m2.isRangeInitialized (allocRange (Size.ofBytes 66) (Size.ofBytes 74)) = .ok (.ok ()) ∧
    (InitMask.new (Size.ofBytes 200) true).get (Size.ofBytes 62) = .ok true ∧
    ∃ b, m2.get (Size.ofBytes 199) = .ok b := by
  let m1 : InitMask :=
    ⟨.Materialized ⟨[0xF000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFF, 0].toArray⟩, Size.ofBytes 200⟩
  let m2 : InitMask :=
    ⟨.Materialized ⟨[0x3000000000000000, 0xFFFFFFFFFFFFFFFC, 0xFFF, 0].toArray⟩, Size.ofBytes 200⟩
  have hwf0 : InitMask.WriteProof.WellFormed (InitMask.new (Size.ofBytes 200) false) := True.intro
  have hwf1 : InitMask.WriteProof.WellFormed m1 := by
    simp only [InitMask.WriteProof.WellFormed]; decide
  have hwf2 : InitMask.WriteProof.WellFormed m2 := by
    simp only [InitMask.WriteProof.WellFormed]; decide
  have hset01 : (InitMask.new (Size.ofBytes 200) false).setRange
      (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok m1 := by
    rw [Mirrors.InitMask.setRange_eq_R]
    simp only [Mirrors.InitMask.setRangeR, Mirrors.InitMask.materialize,
      Mirrors.InitMaskMaterialized.grow, Mirrors.InitMaskMaterialized.setRangeInbounds,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  have hset12 : m1.setRange (allocRange (Size.ofBytes 62) (Size.ofBytes 4)) false = .ok m2 := by
    rw [Mirrors.InitMask.setRange_eq_R]
    simp only [Mirrors.InitMask.setRangeR, Mirrors.InitMaskMaterialized.setRangeInbounds,
      Std.Legacy.Range.forIn_eq_forIn_range']
    decide
  have hset23 : m2.setRange (allocRange Size.ZERO (Size.ofBytes 200)) true =
      .ok (InitMask.new (Size.ofBytes 200) true) := by
    rw [Mirrors.InitMask.setRange_eq_R]
    simp only [Mirrors.InitMask.setRangeR]
    decide
  have hm1_get : ∀ idx : Size, idx.bytes.toNat < 200 → m1.get idx =
      if 60 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 140 then .ok true else .ok false :=
    fun idx hidx => InitMask.WriteProof.set_range_get _ m1 _ (Size.ofBytes 140) idx true
      hwf0 (by decide) (by decide) (by decide) hidx hset01
  have hm2_get : ∀ idx : Size, idx.bytes.toNat < 200 → m2.get idx =
      if 62 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 66 then .ok false else m1.get idx :=
    fun idx hidx => InitMask.WriteProof.set_range_get m1 m2 _ (Size.ofBytes 66) idx false
      hwf1 (by decide) (by decide) (by decide) hidx hset12
  have hg61 : m2.get (Size.ofBytes 61) = .ok true := by
    rw [hm2_get _ (by decide), hm1_get _ (by decide)]; decide
  have hg62 : m2.get (Size.ofBytes 62) = .ok false := by rw [hm2_get _ (by decide)]; decide
  have hg65 : m2.get (Size.ofBytes 65) = .ok false := by rw [hm2_get _ (by decide)]; decide
  have hg66 : m2.get (Size.ofBytes 66) = .ok true := by
    rw [hm2_get _ (by decide), hm1_get _ (by decide)]; decide
  have hm1_66_140 : m1.isRangeInitialized (allocRange (Size.ofBytes 66) (Size.ofBytes 74)) =
      .ok (.ok ()) :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff m1 _ (Size.ofBytes 140)
      hwf1 (by decide) (by decide) (by decide)).1.mpr fun idx hlo hhi => by
      change 66 ≤ idx.bytes.toNat at hlo
      change idx.bytes.toNat < 140 at hhi
      rw [hm1_get idx (Nat.lt_trans hhi (by decide))]
      rw [if_pos_eq ⟨Nat.le_trans (by decide) hlo, hhi⟩]
  have hm2_66_140 : m2.isRangeInitialized (allocRange (Size.ofBytes 66) (Size.ofBytes 74)) =
      .ok (.ok ()) :=
    (InitMask.WriteProof.isRangeInitialized_frame m1 m2
      (allocRange (Size.ofBytes 62) (Size.ofBytes 4))
      (allocRange (Size.ofBytes 66) (Size.ofBytes 74))
      (Size.ofBytes 66) (Size.ofBytes 140) false hwf1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) hset12).mpr hm1_66_140
  have hm3_62 : (InitMask.new (Size.ofBytes 200) true).get (Size.ofBytes 62) = .ok true := by
    have h := InitMask.WriteProof.set_range_get m2 (InitMask.new (Size.ofBytes 200) true)
      (allocRange Size.ZERO (Size.ofBytes 200)) (Size.ofBytes 200) (Size.ofBytes 62) true
      hwf2 (by decide) (by decide) (by decide) (by decide) hset23
    rw [h]; decide
  exact ⟨hset01, hset12, hset23, hg61, hg62, hg65, hg66, hm2_66_140, hm3_62,
    InitMask.WriteProof.get_ok_of_wellFormed m2 (Size.ofBytes 199) hwf2 (by decide)⟩

/-- 8. Exposed-address (`Provenance`, `PointerProvenance.offsetIsAddr = true`)
`Or.inl` branch of `getBytesStripProvenance_ok`, `readScalar_int_roundtrip`, and
`readScalar_int_of_bytes` on an allocation carrying live pointer provenance
(`rangeEmpty = .ok false`, refuting `Or.inr`), pinning the concrete serialized
pointer bytes across both little- and big-endian target layouts. -/
private theorem wit_exposed_provenance_strip_and_transmute (endian : Endian) :
    ∃ (p0 pPtr : Allocation Provenance Unit),
      let layout : TargetDataLayout := ⟨endian, .w64⟩
      let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
      let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
      let r08 := allocRange Size.ZERO (Size.ofBytes 8)
      let subRange := if endian == .little then allocRange Size.ZERO (Size.ofBytes 2)
        else allocRange (Size.ofBytes 6) (Size.ofBytes 2)
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok p0 ∧
      Allocation.writeScalar layout r08 ptrVal p0 = .ok () pPtr ∧
      pPtr.provenanceMap.rangeEmpty r08 (Size.ofBytes 8) = .ok false ∧
      pPtr.getBytesStripProvenance layout r08 =
        .ok (if endian == .little then [0x20, 0x10, 0, 0, 0, 0, 0, 0].toArray
          else [0, 0, 0, 0, 0, 0, 0x10, 0x20].toArray) ∧
      pPtr.readScalar layout r08 false =
        .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 0x1020)) ∧
      pPtr.readScalar layout subRange false =
        (Scalar.fromUInt (BitVec.ofNat 128 0x1020) (Size.ofBytes 2)).mapError AllocError.scalar := by
  let layout : TargetDataLayout := ⟨endian, .w64⟩
  let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
  let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
  let r08 := allocRange Size.ZERO (Size.ofBytes 8)
  have hend08 : r08.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hps_eq : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by
    dsimp only [layout]; decide
  let ⟨pm1, hpm1_ins, hpm1_ptrs⟩ :
      ∃ pm1 : ProvenanceMap Provenance,
        ProvenanceMap.insertPtr Size.ZERO Provenance.wildcard (Size.ofBytes 8) ProvenanceMap.new =
          .ok () pm1 ∧
        pm1.ptrs = [(Size.ZERO, Provenance.wildcard)].toArray :=
    ⟨_, ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      Provenance.wildcard (by decide) hend08, rfl⟩
  have hconvPtr : ptrVal.toBitsOrPtrInternal r08.size = .ok (.pointer ptr) := by
    cases endian <;> decide
  let ⟨p0, hp0, _⟩ := Allocation.tryNew_exists (P := Provenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨hbsP, hlenP, hmutP, _, _, hprovP, hmaskP, _, hwfP, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit p0 hp0
  let ⟨pPtr, hwPtr, _, _, _, _, _, _, hmlPtr, hwfPtr, _, hisPtr, hprovPtr, _, hbytesPtr, _⟩ :=
    Allocation.writeScalar_spec layout p0 r08 ptrVal (.pointer ptr) ProvenanceMap.new pm1
      (by rw [hlenP, hbsP]) hmutP (by rw [hmaskP rfl, hbsP]; rfl) hwfP
      (by decide) (by decide) (by rw [hbsP]; decide) hconvPtr
      (fun _ _ => by
        rw [hprovP, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      ⟨hps_eq.symm, by rw [hps_eq]; exact hpm1_ins⟩
  have hnotEmpty : pPtr.provenanceMap.rangeEmpty r08 (Size.ofBytes 8) = .ok false := by
    rw [hprovPtr]
    unfold ProvenanceMap.rangeEmpty
    rw [Mirrors.ProvenanceMap.rangePtrs_eq_R]
    unfold Mirrors.ProvenanceMap.rangePtrsR Mirrors.ProvenanceMap.adjustedStart
      Mirrors.ProvenanceMap.rangeEnd Mirrors.ProvenanceMap.rangeEntries
    rw [hpm1_ptrs]
    rfl
  have hrawBytes : pPtr.getBytesUnchecked r08 =
      .ok (if endian == .little then [0x20, 0x10, 0, 0, 0, 0, 0, 0].toArray
        else [0, 0, 0, 0, 0, 0, 0x10, 0x20].toArray) := by
    rw [hbytesPtr ptr rfl]
    cases endian <;> decide
  have hstrip : pPtr.getBytesStripProvenance layout r08 =
      .ok (if endian == .little then [0x20, 0x10, 0, 0, 0, 0, 0, 0].toArray
        else [0, 0, 0, 0, 0, 0, 0x10, 0x20].toArray) :=
    (Allocation.getBytesStripProvenance_ok pPtr layout r08 hisPtr (Or.inl rfl)).trans hrawBytes
  have hbv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = (0x1020 : Nat) := by decide
  have hpSlice : pPtr.getBytesUnchecked r08 =
      .ok (Array.ofFn (fun i : Fin r08.size.bytes.toNat =>
        UInt8.ofNat ((HMod.hMod ((HDiv.hDiv (BitVec.ofNat 128 0x1020).toNat (HPow.hPow (2 : Nat) (8 *
          (if layout.endian == .little then i.1 else r08.size.bytes.toNat - i.1 - 1))))) 256)))) := by
    have _h_simpa := hbytesPtr ptr rfl
    simp [hbv] at _h_simpa
    simp
    exact _h_simpa
  have hfromUInt8 : (Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 0x1020) r08.size).mapError
      AllocError.scalar = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 0x1020)) := by decide
  have htransmute8 : pPtr.readScalar layout r08 false =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 0x1020)) :=
    (Allocation.readScalar_int_roundtrip pPtr layout r08 (BitVec.ofNat 128 0x1020)
      hisPtr (by decide) (by decide) (Or.inl rfl) hpSlice).trans hfromUInt8
  have hlenMaskPtr : pPtr.initializationMask.len = Size.ofBytes 8 := by
    rw [hmlPtr, hmaskP rfl]; rfl
  have hallInit : ∀ idx : Size, 0 ≤ idx.bytes.toNat → idx.bytes.toNat < 8 →
      pPtr.initializationMask.get idx = .ok true :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff pPtr.initializationMask r08
      (Size.ofBytes 8) hwfPtr hend08 (by decide) (by rw [hlenMaskPtr]; decide)).1.mp hisPtr
  have hsub : pPtr.readScalar layout
      (if endian == .little then allocRange Size.ZERO (Size.ofBytes 2)
        else allocRange (Size.ofBytes 6) (Size.ofBytes 2)) false =
      (Scalar.fromUInt (BitVec.ofNat 128 0x1020) (Size.ofBytes 2)).mapError AllocError.scalar := by
    cases endian
    · have hinitSub : pPtr.initializationMask.isRangeInitialized
          (allocRange Size.ZERO (Size.ofBytes 2)) = .ok (.ok ()) :=
        (InitMask.WriteProof.isRangeInitialized_nonempty_iff pPtr.initializationMask _
          (Size.ofBytes 2) hwfPtr (by decide) (by decide)
          (by rw [hlenMaskPtr]; decide)).1.mpr fun idx hlo hhi => by
          change idx.bytes.toNat < 2 at hhi
          exact hallInit idx hlo (Nat.lt_trans hhi (by decide))
      have hsliceSub : pPtr.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) =
          .ok [0x20, 0x10].toArray := by
        have hs := Allocation.getBytesUnchecked_subrange pPtr r08
          (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8) (Size.ofBytes 2)
          [0x20, 0x10, 0, 0, 0, 0, 0, 0].toArray hend08 (by decide) (by decide) (by decide) (by decide)
          hrawBytes
        exact hs.trans (by decide)
      change pPtr.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 2)) false = _
      rw [Allocation.readScalar_int_of_bytes pPtr ⟨.little, .w64⟩ _ [0x20, 0x10].toArray
        hinitSub hsliceSub (by decide) (Or.inl rfl)]
      rfl
    · have hinitSub : pPtr.initializationMask.isRangeInitialized
          (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) = .ok (.ok ()) :=
        (InitMask.WriteProof.isRangeInitialized_nonempty_iff pPtr.initializationMask _
          (Size.ofBytes 8) hwfPtr (by decide) (by decide)
          (by rw [hlenMaskPtr]; decide)).1.mpr fun idx hlo hhi => by
          change 6 ≤ idx.bytes.toNat at hlo
          change idx.bytes.toNat < 8 at hhi
          exact hallInit idx (Nat.le_trans (by decide) hlo) hhi
      have hsliceSub : pPtr.getBytesUnchecked (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) =
          .ok [0x10, 0x20].toArray := by
        have hs := Allocation.getBytesUnchecked_subrange pPtr r08
          (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) (Size.ofBytes 8) (Size.ofBytes 8)
          [0, 0, 0, 0, 0, 0, 0x10, 0x20].toArray hend08 (by decide) (by decide) (by decide) (by decide)
          hrawBytes
        exact hs.trans (by decide)
      change pPtr.readScalar ⟨.big, .w64⟩ (allocRange (Size.ofBytes 6) (Size.ofBytes 2)) false = _
      rw [Allocation.readScalar_int_of_bytes pPtr ⟨.big, .w64⟩ _ [0x10, 0x20].toArray
        hinitSub hsliceSub (by decide) (Or.inl rfl)]
      rfl
  exact ⟨p0, pPtr, hp0, hwPtr, hnotEmpty, hstrip, htransmute8, hsub⟩

end NonVacuity
end Anneal.MirCorrespondence.MemoryLemmas
