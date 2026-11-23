-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.MirWp
public import Anneal.ByteRun.Copy

public section

namespace Anneal.ByteRun

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal Anneal.MirWp

/-!
# Mixed-`InitMask` Padded & `Repeat` Canaries (`Anneal.ByteRun.Canaries`)

End-to-end positive, untyped stale-padding preservation, `MirWp` padding-fault
adequacy, and fail-closed negative canaries for `Anneal.ByteRun` (`0`
`noncomputable`, `0` `._unsafe_rec`, `0` `omega`):

1. **12-byte padded `#[repr(C)]` & provenance-mixed aggregate copies
   (`paddedU8U32U8Runs`, `paddedProvMix12Runs`, `canary_padded_struct_copy`):**
   Zero-axiom (`[]`) concrete verification preserving initialized scalar fields,
   `.init b (some prov)` pointer provenance, and `.uninit` padding bytes while
   framing disjoint memory.
2. **36-byte `[PaddedProvMix12; 3]` `Repeat` copy (`canary_repeat_copy`):**
   Zero-axiom (`[]`) verification of 3-element `copyRepeatedlyComp` fusion.
3. **Untyped stale-padding contrast
   (`canary_untyped_padded_copy_preserves_stale_padding`, `[propext]`) & `MirWp`
   padding-read `.undefined` fault adequacy
   (`mirWp_copied_padded_field_ok_and_padding_fault`, `[propext]`):** Proves two
   aggregates equal on all typed fields (`loadIndirectComp`) remain distinct
   after untyped `copyRangeComp` when one carries stale initialized padding
   bytes, and reading a copied `.uninit` padding byte faults with `.undefined`.
4. **Fail-closed negative regression suite
   (`canary_byterun_negative_fail_closed_tests`, `[]`):** Single-cause negative
   checks confirming rejection of zero-size, zero-count, `.shared`, dead,
   out-of-bounds, and unaligned copies.
-/

/-- Canonical 12-byte padded aggregate
`(u8, [u8; 3] uninit pad, u32, u8, [u8; 3] uninit pad)`. -/
@[expose] def paddedU8U32U8Runs (a : UInt8) (b3 b2 b1 b0 : UInt8) (c : UInt8) :
    List ByteRun :=
  [.initPlain [a], .uninitPad 3, .initPlain [b3, b2, b1, b0],
   .initPlain [c], .uninitPad 3]

/-- Provenance-carrying 12-byte mixed aggregate
`(u8, [u8; 3] uninit pad, ptrBytes@prov, u8, [u8; 3] uninit pad)`. -/
@[expose] def paddedProvMix12Runs (a : UInt8) (prov : AllocId) (p3 p2 p1 p0 :
    UInt8)
    (c : UInt8) : List ByteRun :=
  [.initPlain [a], .uninitPad 3, .initProv prov [p3, p2, p1, p0],
   .initPlain [c], .uninitPad 3]

/-- Sample `MemoryState` with `paddedU8U32U8Runs` at `[0..12)` and mutable
destination `[12..24)`. -/
@[expose] def samplePaddedU8U32U8Mem0 : MemoryState :=
  let srcBytes :=
    flattenByteRuns (paddedU8U32U8Runs 0x11 0x22 0x33 0x44 0x55 0x66)
  let dstPreBytes := List.replicate 12 (AllocByte.init 0xFF (some 99))
  let tailBytes := List.replicate 8 AllocByte.uninit
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 3
      mutability := .mut
      bytes := srcBytes ++ dstPreBytes ++ tailBytes
      live := true
    }] }

/-- Sample `MemoryState` with `paddedProvMix12Runs` at `[0..12)` and mutable
destination `[12..24)`. -/
@[expose] def samplePaddedProvMixMem0 : MemoryState :=
  let srcBytes :=
    flattenByteRuns (paddedProvMix12Runs 0x11 7 0xA0 0xA1 0xA2 0xA3 0x66)
  let dstPreBytes := List.replicate 12 (AllocByte.init 0xEE none)
  let tailBytes := List.replicate 8 (AllocByte.init 0x77 (some 88))
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 3
      mutability := .mut
      bytes := srcBytes ++ dstPreBytes ++ tailBytes
      live := true
    }] }

/-- Zero-axiom (`[]`) padded-aggregate `copyRangeComp` canary for both plain
and provenance-carrying 12-byte padded structs. -/
theorem canary_padded_struct_copy :
    (∃ mCopied : MemoryState,
      copyRangeComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 = .ok mCopied ∧
      readBytesComp mCopied ⟨1, 12⟩ 12 2 =
        .ok (flattenByteRuns
          (paddedU8U32U8Runs 0x11 0x22 0x33 0x44 0x55 0x66)) ∧
      readBytesComp mCopied ⟨1, 12⟩ 1 0 = .ok [AllocByte.init 0x11 none] ∧
      (initBytes?Comp [AllocByte.init 0x11 none]).map (decodeUIntComp .big) =
        some 0x11 ∧
      readBytesComp mCopied ⟨1, 16⟩ 4 2 =
        .ok [AllocByte.init 0x22 none, AllocByte.init 0x33 none,
             AllocByte.init 0x44 none, AllocByte.init 0x55 none] ∧
      (initBytes?Comp [AllocByte.init 0x22 none, AllocByte.init 0x33 none,
                       AllocByte.init 0x44 none, AllocByte.init 0x55 none]).map
        (decodeUIntComp .big) = some 0x22334455 ∧
      readBytesComp mCopied ⟨1, 20⟩ 1 0 = .ok [AllocByte.init 0x66 none] ∧
      readBytesComp mCopied ⟨1, 13⟩ 1 0 = .ok [AllocByte.uninit] ∧
      initBytes?Comp [AllocByte.uninit] = none ∧
      initBytes?Comp
        ((flattenByteRuns
          (paddedU8U32U8Runs 0x11 0x22 0x33 0x44 0x55 0x66)).take 4) = none ∧
      readBytesComp mCopied ⟨1, 24⟩ 8 2 =
        .ok (List.replicate 8 AllocByte.uninit)) ∧
    (∃ mProvCopied : MemoryState,
      copyRangeComp samplePaddedProvMixMem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 =
        .ok mProvCopied ∧
      readBytesComp mProvCopied ⟨1, 12⟩ 12 2 =
        .ok (flattenByteRuns
          (paddedProvMix12Runs 0x11 7 0xA0 0xA1 0xA2 0xA3 0x66)) ∧
      readBytesComp mProvCopied ⟨1, 16⟩ 4 2 =
        .ok [AllocByte.init 0xA0 (some 7), AllocByte.init 0xA1 (some 7),
             AllocByte.init 0xA2 (some 7), AllocByte.init 0xA3 (some 7)] ∧
      readBytesComp mProvCopied ⟨1, 24⟩ 8 2 =
        .ok (List.replicate 8 (AllocByte.init 0x77 (some 88)))) :=
  ⟨⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, rfl, rfl, rfl, rfl⟩⟩

/-- Sample `MemoryState` for 3-element `[PaddedProvMix12; 3]` `Repeat` copy. -/
@[expose] def sampleRepeatPaddedMem0 : MemoryState :=
  let srcElem :=
    flattenByteRuns (paddedProvMix12Runs 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F)
  let dstBuf := List.replicate 36 (AllocByte.init 0xCC none)
  let guardTail := List.replicate 4 (AllocByte.init 0x99 (some 55))
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 3
      mutability := .mut
      bytes := srcElem ++ dstBuf ++ guardTail
      live := true
    }] }

/-- Zero-axiom (`[]`) 3-element `[PaddedProvMix12; 3]` `Repeat` copy canary. -/
theorem canary_repeat_copy :
    ∃ mRep3 : MemoryState,
      copyRepeatedlyComp sampleRepeatPaddedMem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 3 =
        .ok mRep3 ∧
      readBytesComp mRep3 ⟨1, 12⟩ 36 2 =
        .ok (flattenByteRuns
          (repeatByteRuns 3
            (paddedProvMix12Runs 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F))) ∧
      readBytesComp mRep3 ⟨1, 12⟩ 12 2 =
        .ok (flattenByteRuns
          (paddedProvMix12Runs 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F)) ∧
      readBytesComp mRep3 ⟨1, 24⟩ 12 2 =
        .ok (flattenByteRuns
          (paddedProvMix12Runs 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F)) ∧
      readBytesComp mRep3 ⟨1, 36⟩ 12 2 =
        .ok (flattenByteRuns
          (paddedProvMix12Runs 0x3A 42 0xB0 0xB1 0xB2 0xB3 0x7F)) ∧
      readBytesComp mRep3 ⟨1, 40⟩ 4 2 =
        .ok [AllocByte.init 0xB0 (some 42), AllocByte.init 0xB1 (some 42),
             AllocByte.init 0xB2 (some 42), AllocByte.init 0xB3 (some 42)] ∧
      readBytesComp mRep3 ⟨1, 37⟩ 3 0 =
        .ok (List.replicate 3 AllocByte.uninit) ∧
      initBytes?Comp (List.replicate 3 AllocByte.uninit) = none ∧
      readBytesComp mRep3 ⟨1, 48⟩ 4 2 =
        .ok (List.replicate 4 (AllocByte.init 0x99 (some 55))) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Companion 12-byte `(u8, u32, u8)` source with stale initialized padding
bytes (`0x99` / `0xAA`) matching `samplePaddedU8U32U8Mem0` on all typed fields.
-/
@[expose] def sampleStaleInitPadMem0 : MemoryState :=
  let srcStale :=
    [AllocByte.init 0x11 none,
     AllocByte.init 0x99 none, AllocByte.init 0x99 none,
     AllocByte.init 0x99 none,
     AllocByte.init 0x22 none, AllocByte.init 0x33 none,
     AllocByte.init 0x44 none, AllocByte.init 0x55 none,
     AllocByte.init 0x66 none,
     AllocByte.init 0xAA none, AllocByte.init 0xAA none,
     AllocByte.init 0xAA none]
  let dstPre := List.replicate 12 (AllocByte.init 0xFF (some 99))
  let tail := List.replicate 8 AllocByte.uninit
  { nextAllocId := 2
    allocations := [{
      allocId := 1
      alignLog2 := 3
      mutability := .mut
      bytes := srcStale ++ dstPre ++ tail
      live := true
    }] }

/-- Untyped stale-padding contrast (`[propext]`): because `copyRangeComp` models
an untyped byte-range copy without typed padding reset, two 12-byte aggregates
agreeing on all three concrete typed field loads (`loadIndirectComp` at `+12`,
`+16`, `+20`) produce distinct copied destination slices (`readBytesComp` at
`⟨1, 12⟩`) and distinct `MemoryState`s when one source carries stale initialized
padding bytes. -/
theorem canary_untyped_padded_copy_preserves_stale_padding :
    ∃ (mOut1 mOut2 : MemoryState),
      copyRangeComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 = .ok mOut1 ∧
      copyRangeComp sampleStaleInitPadMem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 = .ok mOut2 ∧
      mOut1 ≠ mOut2 ∧
      readBytesComp mOut1 ⟨1, 12⟩ 12 2 ≠ readBytesComp mOut2 ⟨1, 12⟩ 12 2 ∧
      loadIndirectComp .big mOut1 (.int .i8 false) ⟨1, 12⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 0x11⟩)) ∧
      loadIndirectComp .big mOut2 (.int .i8 false) ⟨1, 12⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 0x11⟩)) ∧
      loadIndirectComp .big mOut1 (.int .i32 false) ⟨1, 16⟩ =
        .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0x22334455⟩)) ∧
      loadIndirectComp .big mOut2 (.int .i32 false) ⟨1, 16⟩ =
        .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0x22334455⟩)) ∧
      loadIndirectComp .big mOut1 (.int .i8 false) ⟨1, 20⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 0x66⟩)) ∧
      loadIndirectComp .big mOut2 (.int .i8 false) ⟨1, 20⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 0x66⟩)) := by
  refine ⟨_, _, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro hEq
    have hRead := congrArg (fun m => readBytesComp m ⟨1, 13⟩ 1 0) hEq
    nomatch hRead
  · intro hSliceEq
    nomatch hSliceEq

/-- Single-body `Program` reading indirect `u8` local `_1` into `_0`. -/
@[expose] def progReadIndirectU8 : Program := {
  scope := .unit
  pointerWidthBits := 64
  targetEndian := .little
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.int .i8 false, .int .i8 false]
    basicBlocks := [{
      statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
      terminator := .return_
    }]
    identity := "read_indirect_u8"
  }]
}

/-- `Anneal.MirWp` adequacy coupling: reading copied initialized field offset
`12` (`0x11`) satisfies `wpState`, whereas reading copied `.uninit` padding
offset `13` satisfies `wpFaultState ... .undefined`. -/
theorem mirWp_copied_padded_field_ok_and_padding_fault :
    ∃ mCopied : MemoryState,
      copyRangeComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 = .ok mCopied ∧
      wpState progReadIndirectU8 2
        { frames := [{
            defId := 0, blockIdx := 0, stmtIdx := 0,
            locals := [.immediate none, .indirect ⟨1, 12⟩]
          }]
          callerMem := ⟨[]⟩
          mem := mCopied }
        (fun out =>
          out = .returned
            ⟨.scalar ⟨.i8, false, BitVec.ofNat 128 0x11⟩, ⟨[]⟩⟩) ∧
      wpFaultState progReadIndirectU8 2
        { frames := [{
            defId := 0, blockIdx := 0, stmtIdx := 0,
            locals := [.immediate none, .indirect ⟨1, 13⟩]
          }]
          callerMem := ⟨[]⟩
          mem := mCopied }
        .undefined := by
  refine ⟨_, rfl, ?_, ?_⟩
  · exact wpOutcomeState_of_execOutcomeState rfl
  · exact wpOutcomeState_of_execOutcomeState rfl

/-- Zero-axiom (`[]`) single-cause fail-closed negative regression suite:
1. Zero-size `copyRangeComp` (`sz = 0`) rejected with `.unsupported`;
2. Zero-count `copyRepeatedlyComp` (`n = 0`) rejected with `.unsupported`;
3. Zero-element-size `copyRepeatedlyComp` (`elemSz = 0`) rejected;
4. `.shared` destination allocation rejected with `.undefined`;
5. Dead (`live = false`) destination allocation rejected with `.undefined`;
6. Out-of-bounds destination `[28..40)` on 32-byte allocation rejected;
7. Misaligned destination offset `14` (`alignLog2 = 2`) rejected;
8. Misaligned repeat stride (`elemSz = 6`, `alignLog2 = 2`) rejected at `i = 1`.
-/
theorem canary_byterun_negative_fail_closed_tests :
    let sharedDstMem : MemoryState := {
      nextAllocId := 3
      allocations := [
        { allocId := 1, alignLog2 := 2, mutability := .mut,
          bytes := List.replicate 4 (AllocByte.init 0x11 none), live := true },
        { allocId := 2, alignLog2 := 2, mutability := .shared,
          bytes := List.replicate 4 (AllocByte.init 0x00 none), live := true }
      ]
    }
    let deadDstMem : MemoryState := {
      nextAllocId := 3
      allocations := [
        { allocId := 1, alignLog2 := 2, mutability := .mut,
          bytes := List.replicate 4 (AllocByte.init 0x11 none), live := true },
        { allocId := 2, alignLog2 := 2, mutability := .mut,
          bytes := List.replicate 4 (AllocByte.init 0x00 none), live := false }
      ]
    }
    copyRangeComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 12⟩ 0 2 =
      .error .unsupported ∧
    copyRepeatedlyComp sampleRepeatPaddedMem0 ⟨1, 0⟩ ⟨1, 12⟩ 12 2 0 =
      .error .unsupported ∧
    copyRepeatedlyComp sampleRepeatPaddedMem0 ⟨1, 0⟩ ⟨1, 12⟩ 0 2 3 =
      .error .unsupported ∧
    copyRangeComp sharedDstMem ⟨1, 0⟩ ⟨2, 0⟩ 4 2 = .error .undefined ∧
    copyRangeComp deadDstMem ⟨1, 0⟩ ⟨2, 0⟩ 4 2 = .error .undefined ∧
    copyRangeComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 28⟩ 12 2 =
      .error .undefined ∧
    copyRangeComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 14⟩ 12 2 =
      .error .undefined ∧
    copyRepeatedlyComp samplePaddedU8U32U8Mem0 ⟨1, 0⟩ ⟨1, 12⟩ 6 2 2 =
      .error .undefined :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ByteRun

end
