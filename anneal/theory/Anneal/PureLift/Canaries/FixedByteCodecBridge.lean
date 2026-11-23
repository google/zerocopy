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
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Core.BitValidity
public import Anneal.Core.FixedByteCodec
public import Anneal.MirTotal.Ops
public import Anneal.ByteSubLens.Lens
public import Anneal.PureLift.Lens
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.PureLift.FixedByteCodecBridge

public section

namespace Anneal.PureLift

open Anneal.Core Anneal.ByteSubLens Trusted.MirAst Trusted.MirSemantics

/-!
# Verification Canaries for `PureLift.FixedByteCodecBridge`

Kernel-checked positive and negative model-level tests exercising:

1. **Adjacent field writes & whole-struct reinterpretation (`MemoryState`):**
   Writing two adjacent `u16` fields via `typedSubLensPut` into a live
   mutable 4-byte `MemoryState` allocation and reading back as `(u16, u16)`
   and as `u32` across `.little` and `.big` byte orders, alongside lens and
   disjoint-framing laws, dead / out-of-bounds / misaligned rejections, and
   `.shared` allocations outside this `&mut` lens (returning `none`).
2. **Padded `(u16, u8, padUninit 1)` vs. initialized `u32` / `[u8; 4]`:**
   Writing a padded 4-byte record succeeds and reads back cleanly under the
   padded codec while `u32Codec` and `array 4 (u8Codec)` fail closed (`none`),
   contrasted with unpadded `(u16, u8, u8)` → `u32` transmutation soundness.
3. **`PureLift.SpatialPin` freeze / mutate / reabsorb (`LensTestVal`):**
   Freezing `u32` and `Bool` values into `.rawByte` cells, mutating valid
   bytes and reabsorbing updated `u32` values, plus fail-closed `.fail`
   rejection of `.uninit` mutations, padded `padRight (u8Codec .little) 1`
   freezes, invalid `bool` byte `[.rawByte 2]`, and width-`1` smuggled `.init`
   cells.

All tests target `Trusted.MirSemantics.MemoryState` and `PureLift.SymState`
model structures directly (no `rustc` MIR capture or external crate harness
is claimed).
-/

/-! ## 1. `MemoryState` Adjacent `u16 × u16 ↔ u32` & Lens Canaries -/

@[expose] def canaryAllocMem (mu : Mutability) (live : Bool) (alignLog2 : Nat)
    (bytes : List AllocByte) : MemoryState :=
  { nextAllocId := 1
    allocations := [⟨0, alignLog2, mu, bytes, live⟩] }

@[expose] def canaryMem4 : MemoryState :=
  canaryAllocMem .mut true 2 [.uninit, .uninit, .uninit, .uninit]

@[expose] def canaryLensFst16 : ByteSubLens := ⟨0, 0, 2, 1⟩
@[expose] def canaryLensSnd16 : ByteSubLens := ⟨0, 2, 2, 1⟩
@[expose] def canaryLensFull32 : ByteSubLens := ⟨0, 0, 4, 2⟩

private theorem canary_adjacent_lenses :
    AdjacentSubLenses canaryLensFst16 canaryLensSnd16 canaryLensFull32 2 2 where
  pos1 := by decide
  pos2 := by decide
  allocId12 := rfl
  allocId2 := rfl
  offset1 := rfl
  offset2 := rfl
  size1 := rfl
  size2 := rfl
  size12 := rfl
  align1_le := by decide
  align2_le := by decide
  n1_aligned := by decide

/-- Writing two adjacent `u16` fields into `canaryMem4` matches writing the
`prod (u16Codec .little) (u16Codec .little)` codec on `canaryLensFull32` and
reinterprets cleanly as `u32` (`0x12003456` LE / `0x34561200` BE). -/
theorem canary_bridge_adjacent_u16_to_u32 :
    let v1 : BitVec 16 := BitVec.ofNat 16 0x3456
    let v2 : BitVec 16 := BitVec.ofNat 16 0x1200
    (match typedSubLensPut canaryLensFst16 (u16Codec .little) canaryMem4 v1 with
     | some mem1 =>
       match typedSubLensPut canaryLensSnd16 (u16Codec .little) mem1 v2 with
       | some mem2 =>
         typedSubLensGet canaryLensFull32 (u32Codec .little) mem2 =
           some (BitVec.ofNat 32 0x12003456) ∧
         typedSubLensGet canaryLensFull32
             (FixedByteCodec.prod (u16Codec .little) (u16Codec .little)) mem2 =
           some (v1, v2) ∧
         typedSubLensGet canaryLensFull32 (u32Codec .big) mem2 =
           some (BitVec.ofNat 32 0x56340012) ∧
         typedSubLensPut canaryLensFull32
             (FixedByteCodec.prod (u16Codec .little) (u16Codec .little))
             canaryMem4 (v1, v2) = some mem2
       | none => False
     | none => False) ∧
    (match typedSubLensPut canaryLensFst16 (u16Codec .big) canaryMem4 v1 with
     | some mem1 =>
       match typedSubLensPut canaryLensSnd16 (u16Codec .big) mem1 v2 with
       | some mem2 =>
         typedSubLensGet canaryLensFull32 (u32Codec .big) mem2 =
           some (BitVec.ofNat 32 0x34561200)
       | none => False
     | none => False) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Typed lens laws (`get_put`, `put_get_noProv`, `put_put`, disjoint frame),
fail-closed boundary rejections (`live = false`, out-of-bounds, misaligned
parent), and `.shared` allocations outside this `&mut` lens (`none`). -/
theorem canary_bridge_lens_laws_and_rejections :
    let memInit :=
      canaryAllocMem .mut true 2
        [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    let memShared :=
      canaryAllocMem .shared true 2
        [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    let memDead :=
      canaryAllocMem .mut false 2
        [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    let memShort :=
      canaryAllocMem .mut true 2 [.init 1 none, .init 2 none, .init 3 none]
    let memUnaligned :=
      canaryAllocMem .mut true 1
        [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    -- Write then read (`typedSubLens_get_put`):
    (∀ v : BitVec 32,
      ∃ mem',
        typedSubLensPut canaryLensFull32 (u32Codec .little) memInit v =
          some mem' ∧
        typedSubLensGet canaryLensFull32 (u32Codec .little) mem' = some v) ∧
    -- Read provenance-free slice then write back (`put_get_noProv`):
    (match typedSubLensGet canaryLensFull32 (u32Codec .little) memInit with
     | some v =>
       typedSubLensPut canaryLensFull32 (u32Codec .little) memInit v =
         some memInit
     | none => False) ∧
    -- Disjoint field write preserves sibling field:
    (∀ (mem1 : MemoryState) (x : BitVec 16),
      typedSubLensPut canaryLensFst16 (u16Codec .little) memInit x =
        some mem1 →
      typedSubLensGet canaryLensSnd16 (u16Codec .little) mem1 =
        typedSubLensGet canaryLensSnd16 (u16Codec .little) memInit) ∧
    -- Fail-closed boundary guards:
    typedSubLensGet canaryLensFull32 (u32Codec .little) memShared = none ∧
    typedSubLensPut canaryLensFull32 (u32Codec .little) memShared 0 = none ∧
    typedSubLensGet canaryLensFull32 (u32Codec .little) memDead = none ∧
    typedSubLensGet canaryLensFull32 (u32Codec .little) memShort = none ∧
    typedSubLensGet canaryLensFull32 (u32Codec .little) memUnaligned = none := by
  intro memInit memShared memDead memShort memUnaligned
  refine ⟨?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro v
    exact typedSubLens_put_valid_get canaryLensFull32 (u32Codec .little)
      memInit ⟨0, 2, .mut, [.init 1 none, .init 2 none, .init 3 none, .init 4 none], true⟩
      v (by decide) rfl rfl rfl rfl rfl rfl
  · intro mem1 x hPut
    exact typedSubLens_get_put_disjoint canaryLensFst16 canaryLensSnd16
      (u16Codec .little) (u16Codec .little) memInit mem1 x (by decide) hPut

/-! ## 2. Padded `(u16, u8, padUninit 1)` vs. Unpadded `(u16, u8, u8)` -/

@[expose] def paddedU16U8Codec (endian : TargetEndian) :
    FixedByteCodec (BitVec 16 × BitVec 8) 4 :=
  FixedByteCodec.padRight
    (FixedByteCodec.prod (u16Codec endian) (u8Codec endian)) 1

@[expose] def unpaddedU16U8U8Codec (endian : TargetEndian) :
    FixedByteCodec (BitVec 16 × (BitVec 8 × BitVec 8)) 4 :=
  FixedByteCodec.prod (u16Codec endian)
    (FixedByteCodec.prod (u8Codec endian) (u8Codec endian))

/-- Writing padded `(u16, u8, padUninit 1)` into `canaryMem4` reads back
under the padded codec while causing `u32Codec` and `array 4 (u8Codec)` to
return `none`; unpadded `(u16, u8, u8)` transmutes soundly into `u32`. -/
theorem canary_bridge_padding_and_transmute (endian : TargetEndian)
    (a : BitVec 16) (b b2 : BitVec 8) :
    (match typedSubLensPut canaryLensFull32 (paddedU16U8Codec endian)
        canaryMem4 (a, b) with
     | some memPadded =>
       typedSubLensGet canaryLensFull32 (paddedU16U8Codec endian) memPadded =
         some (a, b) ∧
       typedSubLensGet canaryLensFull32 (u32Codec endian) memPadded = none ∧
       typedSubLensGet canaryLensFull32
         (FixedByteCodec.array 4 (u8Codec endian)) memPadded = none
     | none => False) ∧
    (∃ memUnp : MemoryState,
      typedSubLensPut canaryLensFull32 (unpaddedU16U8U8Codec endian)
        canaryMem4 (a, (b, b2)) = some memUnp ∧
      ∃ w : BitVec 32,
        typedSubLensGet canaryLensFull32 (u32Codec endian) memUnp = some w) := by
  have hPadValid :=
    typedSubLens_put_valid_get canaryLensFull32 (paddedU16U8Codec endian)
      canaryMem4 ⟨0, 2, .mut, [.uninit, .uninit, .uninit, .uninit], true⟩
      (a, b) (by decide) rfl rfl rfl rfl rfl rfl
  have ⟨memPad, hPutPad, hGetPad⟩ := hPadValid
  have hUnpValid :=
    typedSubLens_put_valid_get canaryLensFull32 (unpaddedU16U8U8Codec endian)
      canaryMem4 ⟨0, 2, .mut, [.uninit, .uninit, .uninit, .uninit], true⟩
      (a, (b, b2)) (by decide) rfl rfl rfl rfl rfl rfl
  have ⟨memUnp, hPutUnp, _⟩ := hUnpValid
  have hUnpInit : (unpaddedU16U8U8Codec endian).IsInitCodec :=
    FixedByteCodec.prod_isInitCodec
      (uintBvCodec_isInitCodec endian 2 (by decide))
      (FixedByteCodec.prod_isInitCodec
        (uintBvCodec_isInitCodec endian 1 (by decide))
        (uintBvCodec_isInitCodec endian 1 (by decide)))
  have hUnpNoProv : (unpaddedU16U8U8Codec endian).NoProvCodec :=
    FixedByteCodec.prod_noProvCodec
      (uintBvCodec_noProvCodec endian 2 (by decide))
      (FixedByteCodec.prod_noProvCodec
        (uintBvCodec_noProvCodec endian 1 (by decide))
        (uintBvCodec_noProvCodec endian 1 (by decide)))
  have hU32Surj : (u32Codec endian).IsSurjectiveInitDecoder :=
    uintBvCodec_isSurjectiveInitDecoder endian 4 (by decide)
  refine ⟨?_, ⟨memUnp, hPutUnp, ?_⟩⟩
  · rw [hPutPad]
    exact ⟨hGetPad,
      typedSubLens_padRight_uintBvCodec_none endian canaryLensFull32
        (FixedByteCodec.prod (u16Codec endian) (u8Codec endian))
        (by decide) (by decide) canaryMem4 memPad (a, b) hPutPad,
      typedSubLens_padRight_array_none canaryLensFull32
        (FixedByteCodec.prod (u16Codec endian) (u8Codec endian))
        (u8Codec endian) (by decide) (by decide : 3 + 1 = 4 * 1)
        (initDecoded_uintBvCodec endian 1 (by decide))
        canaryMem4 memPad (a, b) hPutPad⟩
  · exact typedSubLens_transmute_of_traits canaryLensFull32
      (unpaddedU16U8U8Codec endian) (u32Codec endian) hUnpInit hUnpNoProv
      hU32Surj canaryMem4 memUnp (a, (b, b2)) hPutUnp

/-! ## 3. `PureLift.SpatialPin` Freeze / Mutate / Reabsorb Canaries -/

@[expose] def lensU32ToVal (x : BitVec 32) : LensTestVal := .atom x.toNat

@[expose] def lensValToU32 (v : LensTestVal) : Option (BitVec 32) :=
  match v with
  | ⟨_, .atom k⟩ =>
    if Nat.blt k (Nat.pow 2 32) then some (BitVec.ofNat 32 k) else none
  | _ => none

theorem lensU32_roundtrip (v : LensTestVal) (x : BitVec 32)
    (h : lensValToU32 v = some x) : lensU32ToVal x = v := by
  cases v with
  | mk f tree =>
    cases tree with
    | atom k =>
      dsimp only [lensValToU32] at h
      cases hLt : Nat.blt k (Nat.pow 2 32) with
      | false =>
        change (if Nat.blt k (Nat.pow 2 32) then some (BitVec.ofNat 32 k)
          else none) = some x at h
        rw [hLt] at h
        nomatch h
      | true =>
        change (if Nat.blt k (Nat.pow 2 32) then some (BitVec.ofNat 32 k)
          else none) = some x at h
        rw [hLt] at h
        injection h with hx
        subst hx
        dsimp only [lensU32ToVal]
        have hK : k < Nat.pow 2 32 := Nat.le_of_ble_eq_true hLt
        have hMod : (BitVec.ofNat 32 k).toNat = k := by
          change Nat.mod k (Nat.pow 2 32) = k
          exact Nat.mod_eq_of_lt hK
        rw [hMod]
        rfl
    | ref _ _ | branch _ _ _ _ | choice _ _ _ _ _ _ => nomatch h

@[expose] def lensBoolToVal (b : Bool) : LensTestVal :=
  .atom (if b then 1 else 0)

@[expose] def lensValToBool (v : LensTestVal) : Option Bool :=
  match v with
  | ⟨_, .atom 0⟩ => some false
  | ⟨_, .atom 1⟩ => some true
  | _ => none

theorem lensBool_roundtrip (v : LensTestVal) (b : Bool)
    (h : lensValToBool v = some b) : lensBoolToVal b = v := by
  cases v with
  | mk f tree =>
    cases tree with
    | atom k =>
      cases k with
      | zero =>
        injection h with hb
        subst hb
        rfl
      | succ k' =>
        cases k' with
        | zero =>
          injection h with hb
          subst hb
          rfl
        | succ _ => nomatch h
    | ref _ _ | branch _ _ _ _ | choice _ _ _ _ _ _ => nomatch h

@[expose] def lensU8ToVal (x : BitVec 8) : LensTestVal := .atom x.toNat

@[expose] def lensValToU8 (v : LensTestVal) : Option (BitVec 8) :=
  match v with
  | ⟨_, .atom k⟩ =>
    if Nat.blt k (Nat.pow 2 8) then some (BitVec.ofNat 8 k) else none
  | _ => none

theorem lensU8_roundtrip (v : LensTestVal) (x : BitVec 8)
    (h : lensValToU8 v = some x) : lensU8ToVal x = v := by
  cases v with
  | mk f tree =>
    cases tree with
    | atom k =>
      dsimp only [lensValToU8] at h
      cases hLt : Nat.blt k (Nat.pow 2 8) with
      | false =>
        change (if Nat.blt k (Nat.pow 2 8) then some (BitVec.ofNat 8 k)
          else none) = some x at h
        rw [hLt] at h
        nomatch h
      | true =>
        change (if Nat.blt k (Nat.pow 2 8) then some (BitVec.ofNat 8 k)
          else none) = some x at h
        rw [hLt] at h
        injection h with hx
        subst hx
        dsimp only [lensU8ToVal]
        have hK : k < Nat.pow 2 8 := Nat.le_of_ble_eq_true hLt
        have hMod : (BitVec.ofNat 8 k).toNat = k := by
          change Nat.mod k (Nat.pow 2 8) = k
          exact Nat.mod_eq_of_lt hK
        rw [hMod]
        rfl
    | ref _ _ | branch _ _ _ _ | choice _ _ _ _ _ _ => nomatch h

@[expose] def spatialU32Codec : SpatialCodec LensTestVal :=
  spatialCodecOfFixedByteCodec 201 (u32Codec .little)
    (uintBvCodec_noProvCodec .little 4 (by decide))
    lensU32ToVal lensValToU32 lensU32_roundtrip

@[expose] def spatialBoolCodec : SpatialCodec LensTestVal :=
  spatialCodecOfFixedByteCodec 202 boolCodec
    boolCodec_noProvCodec lensBoolToVal lensValToBool lensBool_roundtrip

@[expose] def spatialPadU8Codec : SpatialCodec LensTestVal :=
  spatialCodecOfFixedByteCodec 203
    (FixedByteCodec.padRight (u8Codec .little) 1)
    (FixedByteCodec.padRight_noProvCodec 1
      (uintBvCodec_noProvCodec .little 1 (by decide)))
    lensU8ToVal lensValToU8 lensU8_roundtrip

/-- End-to-end `PureLift.SpatialPin` + `FixedByteCodec` canaries:
1. Freezing `0x12345678` under `spatialU32Codec` yields `.rawByte` cells with
   `hasUninitCell = false`, mutating to `[1, 2, 3, 4]` reabsorbs `.atom
   0x04030201`, and immediate freeze+reabsorb preserves `0x12345678`.
2. Replacing any spatial cell with `.uninit` rejects reabsorption (`.fail`).
3. Freezing padded `padRight (u8Codec .little) 1` emits `.uninit` so
   `freezeToSpatialInState` fails closed (`.fail`), and a pre-pinned spatial
   block holding `[.rawByte 5, .uninit]` also fails reabsorption (`.fail`).
4. Mutating `spatialBoolCodec` to `[.rawByte 2]` or smuggling width-`1`
   `[.init (.atom 999)]` rejects reabsorption (`.fail`), while non-`u32`
   handles (`.ref 3 []`) still satisfy `LawfulCodec` at length `4 + 1`. -/
theorem canary_bridge_spatial_pin_lifecycle :
    let stU32 : SymState LensTestVal :=
      { locals := [⟨.atom 0x12345678, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 0x12345678, .unborrowed⟩,
                    .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stBool : SymState LensTestVal :=
      { locals := [⟨.atom 1, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 1, .unborrowed⟩,
                    .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stPad : SymState LensTestVal :=
      { locals := [⟨.atom 5, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 5, .unborrowed⟩,
                    .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stPadManuallyPinned : SymState LensTestVal :=
      { locals := [⟨.atom 5, .mutLocked 0⟩]
        loans := [⟨0, .spatialPinned 0 spatialPadU8Codec,
                    ⟨.atom 5, .unborrowed⟩, .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := [⟨0, 0, .readWrite, 0, 0, [.rawByte 5, .uninit]⟩]
        nextSpatialTag := 1 }
    -- 1. Valid freeze -> mutate -> reabsorb:
    (hasUninitCell (spatialU32Codec.encode (.atom 0x12345678)) = false ∧
      spatialU32Codec.encode (.atom 0x12345678) =
        [.rawByte 0x78, .rawByte 0x56, .rawByte 0x34, .rawByte 0x12] ∧
      (match freezeToSpatialInState lensTestValAlg 0 spatialU32Codec stU32 with
       | .ok stPin =>
         (match reabsorbFromSpatialInState lensTestValAlg 0
             spatialU32Codec stPin with
          | .ok stBack =>
            (match findLoan 0 stBack.loans with
             | some e => e.cell.val = .atom 0x12345678
             | none => False)
          | .fail => False) ∧
         (match mutateSpatialInState 0 0
             [.rawByte 0x01, .rawByte 0x02, .rawByte 0x03, .rawByte 0x04]
             stPin with
          | .ok stMut =>
            (match reabsorbFromSpatialInState lensTestValAlg 0
                spatialU32Codec stMut with
             | .ok stDone =>
               (match findLoan 0 stDone.loans with
                | some e => e.cell.val = .atom 0x04030201 ∧
                  stDone.spatial = []
                | none => False)
             | .fail => False)
          | .fail => False) ∧
         -- 2. `.uninit` mutation fails reabsorption:
         (match mutateSpatialInState 0 0
             [.rawByte 0x01, .rawByte 0x02, .rawByte 0x03, .uninit]
             stPin with
          | .ok stBadUninit =>
            reabsorbFromSpatialInState lensTestValAlg 0
              spatialU32Codec stBadUninit = .fail
          | .fail => False)
       | .fail => False)) ∧
    -- 3. Padded `padRight` emits `.uninit`, failing both freeze & reabsorb:
    (hasUninitCell (spatialPadU8Codec.encode (.atom 5)) = true ∧
      freezeToSpatialInState lensTestValAlg 0 spatialPadU8Codec stPad = .fail ∧
      reabsorbFromSpatialInState lensTestValAlg 0
        spatialPadU8Codec stPadManuallyPinned = .fail) ∧
    -- 4. Bool invalid byte `[.rawByte 2]`, width-1 `.init` smuggle, & `.ref`:
    (match freezeToSpatialInState lensTestValAlg 0 spatialBoolCodec stBool with
     | .ok stBoolPin =>
       (match mutateSpatialInState 0 0 [.rawByte 2] stBoolPin with
        | .ok stBadBool =>
          reabsorbFromSpatialInState lensTestValAlg 0
            spatialBoolCodec stBadBool = .fail
        | .fail => False) ∧
       (match mutateSpatialInState 0 0 [.init (.atom 999)] stBoolPin with
        | .ok stSmuggle =>
          reabsorbFromSpatialInState lensTestValAlg 0
            spatialBoolCodec stSmuggle = .fail
        | .fail => False)
     | .fail => False) ∧
    spatialU32Codec.decode (spatialU32Codec.encode (.ref 3 [])) =
      some (.ref 3 []) :=
  ⟨⟨rfl, rfl, ⟨rfl, ⟨⟨rfl, rfl⟩, rfl⟩⟩⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

end Anneal.PureLift

end
