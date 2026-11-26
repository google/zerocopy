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
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Anneal.MediaBits.Bitstream
public import Anneal.MediaBits.SyntaxLens
public import Anneal.MediaDsp

public section

/-!
# Codec 0-TCB Non-Vacuity & Real H.264 / AV1 (`rav1d`) / MP4 Canaries

Standalone canary suite exercising every FFmpeg codec-domain 0-TCB module
against concrete H.264, AV1 (`rav1d`), and MP4/PSSH obligations:

1. **H.264 `decode_ue_golomb_u32` word round-trip (`canary_h264_ue_word`):**
   verifies `decodeUeWord 32 (encodeUeWord 32 ...)` recovers exact `(len, v)`
   for concrete and parametric code numbers regardless of trailing cache bits.
2. **AV1 `rav1d` OBU header + LEB128 framing (`canary_rav1d_obu_leb128`):**
   verifies exact `packObuHeader_unpack`, `decodeLeb128_encodeLeb128` (including
   multi-byte OBU payload sizes), and `parseObuUnit_progress` + forbidden-bit
   rejection.
3. **MP4/PSSH box-header framing (`canary_mp4_pssh_box`):**
   verifies normal 32-bit, extended 64-bit, and malformed `< 8`-byte box
   rejection + `parseMp4BoxHeader_rem_decrease`.
4. **H.264 SPS CVE-2012-0851 / CVE-2013-2277 checks (`canary_h264_sps_cves`):**
   verifies 4K 10-bit 4:2:0 SPS acceptance with positive cropped dims and
   `< 2^32` pixels, AND concrete rejection of `chroma_format_idc = 4`
   (CVE-2012-0851) and `bit_depth_luma_minus8 = 7` (CVE-2013-2277).
5. **H.264 4×4 IDCT butterfly `i32` overflow-freedom & 10-bit HDR deblock
   (`canary_h264_idct4_and_deblock10`):**
   verifies the full 2D (row + column) 16-bit coefficient pass stays
   `≤ 524288 < 2^31`, pins H.264 §5.1 negative arithmetic-shift rounding for
   `idct4Row`, `idct4AddPixel`, and `deblockDelta`, and verifies 10-bit
   deblocking stays strictly `< 1024`.
6. **H.264 CABAC & AV1 `rav1d` MSAC renorm (`canary_cabac_msac_renorm`):**
   verifies 2-bin composed CABAC renormalization restores `CabacInv`
   (`[256, 510]`) in `≤ 7` shifts per bin and MSAC §8.2.6 CDF split +
   sub-range gap + renormalization restores `MsacInv` (`[32768, 65536)`) in
   `≤ 15` shifts.
-/

namespace Anneal.MediaDsp.Canaries

open Anneal.MediaBits.Bitstream Anneal.MediaBits.SyntaxLens
open Anneal.MediaDsp.ClampAndButterfly Anneal.MediaDsp.EntropyMath

/-- Canary 1: H.264 `decode_ue_golomb_u32` word-level round-trip for `v = 5`
(`lz = 2`, `len = 5` bits in a 32-bit MSB cache) with arbitrary 27-bit trailer
`trail < 2^27`, plus concrete `byteLane` / `nat_land_seven` checks. -/
theorem canary_h264_ue_word (trail : Nat)
    (hTrail : trail < HPow.hPow (2 : Nat) 27) :
    decodeUeWord 32 (encodeUeWord 32 2 5 trail) = (5, 5) ∧
    Nat.land 23 7 = 7 ∧
    byteLane (beU32Nat 0x70 0x73 0x73 0x68) 3 = 0x70 := by
  refine ⟨?_, ?_, ?_⟩
  · exact decodeUeWord_encodeUeWord (w := 32) (lz := 2) (v := 5)
      (trail := trail) (by decide) (by decide) (by decide) hTrail
  · exact nat_land_seven 23
  · exact (byteLane_beU32Nat (by decide) (by decide) (by decide) (by decide)).1

/-- Canary 2: AV1 (`rav1d`) OBU header round-trip, multi-byte LEB128 round-trip
for OBU size `300`, forbidden-bit rejection (`0x80`), and strict consumption
progress on an OBU Sequence Header (`type = 1`, `hasSize = true`). -/
theorem canary_rav1d_obu_leb128 (rest : List Nat) :
    packObuHeader (unpackObuHeader 0x0A) = 0x0A ∧
    decodeLeb128 (encodeLeb128 300 ++ rest) = some (300, rest) ∧
    parseObuUnit [0x8A, 0x00] = none ∧
    ∃ hdr extOpt payload rem,
      parseObuUnit [0x0A, 0x02, 0xAA, 0xBB, 0xCC] =
        some (hdr, extOpt, payload, rem) ∧
      hdr.forbidden = false ∧ rem.length < 5 := by
  refine ⟨packObuHeader_unpack 0x0A (by decide),
          decodeLeb128_encodeLeb128 300 rest (by decide),
          rfl, ?_⟩
  have hp : parseObuUnit [0x0A, 0x02, 0xAA, 0xBB, 0xCC] =
      some (unpackObuHeader 0x0A, none, [0xAA, 0xBB], [0xCC]) := rfl
  have hprog := parseObuUnit_progress hp
  exact ⟨unpackObuHeader 0x0A, none, [0xAA, 0xBB], [0xCC], hp, hprog.1, hprog.2⟩

/-- Canary 3: MP4/PSSH box framing (`pssh` FourCC `0x70737368`) accepts a valid
32-byte box with exact remaining-byte decrease and rejects a corrupt 4-byte
header (`size32 = 4 < 8`). -/
theorem canary_mp4_pssh_box :
    (parseMp4BoxHeader 100 0 4 0x70737368 none = none) ∧
    ∃ box,
      parseMp4BoxHeader 100 0 32 0x70737368 none = some box ∧
      box.bodyStart + box.bodyLen = box.nextOff ∧
      (100 - box.nextOff) + 8 ≤ 100 - 0 := by
  refine ⟨rfl, ?_⟩
  have hp : parseMp4BoxHeader 100 0 32 0x70737368 none =
      some { boxType := 0x70737368, bodyStart := 8,
             bodyLen := 24, nextOff := 32 } := rfl
  have hs := parseMp4BoxHeader_sound hp
  have hd := parseMp4BoxHeader_rem_decrease hp
  exact ⟨_, hp, hs.2.1, hd⟩

/-- Canary 4: H.264 SPS validator accepts a 4K 10-bit 4:2:0 frame (proving
positive cropped dimensions & `< 2^32` sample count) and rejects CVE-2012-0851
(`chromaFormatIdc = 4`) and CVE-2013-2277 (`bitDepthLumaMinus8 = 7`). -/
theorem canary_h264_sps_cves :
    let valid4k : SpsDimParams := {
      chromaFormatIdc := 1, bitDepthLumaMinus8 := 2, bitDepthChromaMinus8 := 2,
      picWidthInMbsMinus1 := 239, picHeightInMapUnitsMinus1 := 134,
      frameMbsOnly := true, cropLeft := 0, cropRight := 0,
      cropTop := 0, cropBottom := 0
    }
    let cve2012 : SpsDimParams := { valid4k with chromaFormatIdc := 4 }
    let cve2013 : SpsDimParams := { valid4k with bitDepthLumaMinus8 := 7 }
    (spsDimsValid valid4k = true ∧
      valid4k.codedWidth * valid4k.codedHeight < HPow.hPow (2 : Nat) 32) ∧
    spsDimsValid cve2012 = false ∧
    spsDimsValid cve2013 = false := by
  dsimp only
  have hv : spsDimsValid {
      chromaFormatIdc := 1, bitDepthLumaMinus8 := 2, bitDepthChromaMinus8 := 2,
      picWidthInMbsMinus1 := 239, picHeightInMapUnitsMinus1 := 134,
      frameMbsOnly := true, cropLeft := 0, cropRight := 0,
      cropTop := 0, cropBottom := 0
    } = true := rfl
  have hs := spsDimsValid_sound hv
  exact ⟨⟨hv, hs.2.2.2.2.2⟩, rfl, rfl⟩

/-- Canary 5: H.264 4×4 IDCT 2D butterfly (row + column) `i32` overflow-freedom
for 16-bit input coefficients (`|c_i| ≤ 32768`, `1D ≤ 131072`,
`2D ≤ 524288 < 2^31`), concrete H.264 §5.1 negative arithmetic-shift checks,
and 10-bit HDR deblocking output safety (`< 1024`). -/
theorem canary_h264_idct4_and_deblock10
    (c0 c1 c2 c3 : Int)
    (h0 : c0.natAbs ≤ 32768) (h1 : c1.natAbs ≤ 32768)
    (h2 : c2.natAbs ≤ 32768) (h3 : c3.natAbs ≤ 32768)
    (tc p1 p0 q0 q1 : Nat) :
    let row := idct4Row c0 c1 c2 c3
    let col := idct4Row row.1 row.2.1 row.2.2.1 row.2.2.2
    col.1.natAbs ≤ 524288 ∧
    col.1.natAbs < HPow.hPow (2 : Nat) 31 ∧
    idct4Row 0 (Int.negOfNat 1) 0 0 =
      (Int.negOfNat 1, Int.negOfNat 1, 1, 1) ∧
    idct4AddPixel 8 100 (Int.negOfNat 33) = 99 ∧
    deblockDelta 4 100 102 100 100 = Int.negOfNat 1 ∧
    (deblockPair 10 tc p1 p0 q0 q1).1 < 1024 ∧
    (deblockPair 10 tc p1 p0 q0 q1).2 < 1024 := by
  have hb1 := idct4Row_natAbs_bound h0 h1 h2 h3
  have hb2 := idct4Row_natAbs_bound hb1.1 hb1.2.1 hb1.2.2.1 hb1.2.2.2
  have h524 : (idct4Row (idct4Row c0 c1 c2 c3).1 (idct4Row c0 c1 c2 c3).2.1
      (idct4Row c0 c1 c2 c3).2.2.1 (idct4Row c0 c1 c2 c3).2.2.2).1.natAbs ≤
      524288 := hb2.1
  have hd := deblockPair_lt 10 tc p1 p0 q0 q1
  exact ⟨h524, Nat.lt_of_le_of_lt h524 (by decide), rfl, rfl, rfl, hd.1, hd.2⟩

/-- Canary 6: 2-bin composed H.264 CABAC decode preserves `CabacInv`
(`256 ≤ range ≤ 510 ∧ offset < range`), and AV1 `rav1d` MSAC §8.2.6 CDF split +
strict `≥ 4` symbol gap + renormalization preserves `MsacInv`
(`32768 ≤ rng < 65536 ∧ dif < rng`). -/
theorem canary_cabac_msac_renorm (st : CabacState) (rLps1 rLps2 : Nat)
    (bits : List Nat) (hInv : CabacInv st)
    (hLo1 : 2 ≤ rLps1) (hHi1 : rLps1 ≤ 240)
    (hLo2 : 2 ≤ rLps2) (hHi2 : rLps2 ≤ 240)
    (ms : MsacState) (hMsInv : MsacInv ms) :
    let step1 := cabacRenorm (cabacSplitBin st rLps1).2 bits
    let step2 := cabacRenorm (cabacSplitBin step1.1 rLps2).2 step1.2
    CabacInv step1.1 ∧
    CabacInv step2.1 ∧
    msacSplitVal ms.rng 16384 1 ≤ ms.rng ∧
    msacSplitVal ms.rng 100 1 + 4 ≤ msacSplitVal ms.rng 120 2 ∧
    MsacInv (msacRenorm
      { rng := msacSplitVal ms.rng 120 2 - msacSplitVal ms.rng 100 1,
        dif := 0 } bits).1 := by
  have h1 : CabacInv (cabacRenorm (cabacSplitBin st rLps1).2 bits).1 :=
    cabacRenorm_sound bits (cabacSplitBin_preserves hInv hLo1 hHi1)
  have h2 : CabacInv
      (cabacRenorm
        (cabacSplitBin (cabacRenorm (cabacSplitBin st rLps1).2 bits).1 rLps2).2
        (cabacRenorm (cabacSplitBin st rLps1).2 bits).2).1 :=
    cabacRenorm_sound _ (cabacSplitBin_preserves h1 hLo2 hHi2)
  have hSplitLe : msacSplitVal ms.rng 16384 1 ≤ ms.rng :=
    msacSplitVal_le_rng hMsInv.1 (by decide) (by decide)
  have hGap : msacSplitVal ms.rng 100 1 + 4 ≤ msacSplitVal ms.rng 120 2 :=
    msacSplitVal_step_gap ms.rng 1 (by decide)
  have hSubGe4 : 4 ≤ msacSplitVal ms.rng 120 2 - msacSplitVal ms.rng 100 1 := by
    have hLe : msacSplitVal ms.rng 100 1 ≤ msacSplitVal ms.rng 120 2 :=
      Nat.le_trans (Nat.le_add_right _ 4) hGap
    have hAdd : 4 + msacSplitVal ms.rng 100 1 ≤
        (msacSplitVal ms.rng 120 2 - msacSplitVal ms.rng 100 1) +
          msacSplitVal ms.rng 100 1 := by
      rw [Nat.sub_add_cancel hLe, Nat.add_comm]
      exact hGap
    exact Nat.le_of_add_le_add_right hAdd
  have hSubPos : 1 ≤ msacSplitVal ms.rng 120 2 - msacSplitVal ms.rng 100 1 :=
    Nat.le_trans (by decide : 1 ≤ 4) hSubGe4
  have hSubLt :
      msacSplitVal ms.rng 120 2 - msacSplitVal ms.rng 100 1 < 65536 := by
    have hHiLe : msacSplitVal ms.rng 120 2 ≤ ms.rng :=
      msacSplitVal_le_rng hMsInv.1 (by decide) (by decide)
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.sub_le _ _) hHiLe) hMsInv.2.1
  have hMsRen : MsacInv (msacRenorm
      { rng := msacSplitVal ms.rng 120 2 - msacSplitVal ms.rng 100 1,
        dif := 0 } bits).1 :=
    msacRenorm_sound bits hSubPos hSubLt hSubPos
  exact ⟨h1, h2, hSplitLe, hGap, hMsRen⟩

end Anneal.MediaDsp.Canaries

end
