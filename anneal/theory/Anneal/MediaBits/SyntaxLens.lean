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
public import Init.Data.List.Basic
public import Anneal.InitLemmas
public import Anneal.MediaBits.Bitstream

public section

/-!
# Codec Container & Header Syntax Lenses (`Anneal.MediaBits.SyntaxLens`)

Zero-duplication, 0-TCB, Pass-1-pure (`prelude` + locked `Init.*` +
`Anneal.InitLemmas` + `Anneal.MediaBits.Bitstream`, zero `._unsafe_rec`,
zero `omega`, axioms `⊆ [propext, Quot.sound]`, zero `Classical.choice`)
container and header framing lenses for video demuxers and bitstream parsers:

1. **ISOBMFF / MP4 Box-Header Framing (`Mp4BoxSlice`, `parseMp4BoxHeader`):**
   - Standard 32-bit size (`≥ 8`), 64-bit extended size (`size32 == 1 → ≥ 16`),
     and EOF box (`size32 == 0`).
   - Proves exact slice confinement (`bodyStart + bodyLen = nextOff ≤ bufLen`),
     strict forward progress (`off + 8 ≤ nextOff`), and a finite box-chain step
     bound (`≤ (bufLen - off) / 8`), directly backing `parse_mp4_pssh_chain`.
2. **AV1 (`rav1d`) OBU Header Bit-Lens (`ObuHeader`, `unpackObuHeader`,
   `packObuHeader`, `parseObuUnit`):**
   - Exact bit-field unpacking (`forbidden`, `obuType : 4b`, `hasExt`,
     `hasSize`, `reserved`) with `unpackObuHeader_type_lt`, `packObuHeader_lt`,
     and `packObuHeader_unpack` round-trip proof.
   - Composes directly with `Anneal.MediaBits.Bitstream.decodeLeb128` to frame
     OBU payload slices with strict forward progress (`rem.length < bs.length`).
3. **H.264 §7.4.2.1.1 SPS Frame-Dimension & Chroma-Crop Validator
   (`h264SubWidthC`, `h264SubHeightC`, `SpsDimParams`, `spsDimsValid`):**
   - Exact macroblock dimension expansion (`16 * (picWidthInMbsMinus1 + 1)`),
     chroma subsampling factors (`h264SubWidthC`, `h264SubHeightC`), bit-depth
     bounds (`8 ≤ bd ≤ 14`, preventing CVE-2013-2277), chroma format bounds
     (`≤ 3`, preventing CVE-2012-0851), and positive overflow-free dimensions
     (`0 < croppedWidth`, `0 < croppedHeight`,
     `codedWidth * codedHeight < 2^32`), matching
     `validate_h264_sps_frame_dims`.
-/

namespace Anneal.MediaBits.SyntaxLens

open Anneal.InitLemmas Anneal.MediaBits.Bitstream

private theorem ble_true_iff_le :
    ∀ a b : Nat, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | _ + 1, 0 =>
    ⟨fun h => Bool.noConfusion h,
     fun h => False.elim (Nat.not_succ_le_zero _ h)⟩
  | a + 1, b + 1 => by
    dsimp only [Nat.ble]
    exact ⟨fun h => Nat.succ_le_succ ((ble_true_iff_le a b).mp h),
           fun h => (ble_true_iff_le a b).mpr (Nat.le_of_succ_le_succ h)⟩

private theorem blt_true_iff_lt (a b : Nat) : Nat.blt a b = true ↔ a < b :=
  ble_true_iff_le (a + 1) b

/-! ## Part 1: ISOBMFF / MP4 Box-Header Framing (`parse_mp4_pssh_chain`) -/

/-- Validated MP4/ISOBMFF box slice inside a buffer of length `bufLen`. -/
structure Mp4BoxSlice where
  /-- FourCC box type (packed big-endian `u32`). -/
  boxType : Nat
  /-- Byte offset where box payload starts (`off + 8` or `off + 16`). -/
  bodyStart : Nat
  /-- Byte length of box payload. -/
  bodyLen : Nat
  /-- Byte offset of the next sibling box (`bodyStart + bodyLen`). -/
  nextOff : Nat

/-- Parse one ISOBMFF/MP4 box header at offset `off` inside a buffer of total
length `bufLen`, given the already-read 32-bit `size32`, 32-bit `boxType`, and
optional 64-bit extended size `extSize64` (present when `off + 16 ≤ bufLen`).
Rejects truncated headers, sizes `< 8` (or `< 16` for extended boxes), and
boxes extending past `bufLen`. -/
@[expose] def parseMp4BoxHeader (bufLen off size32 boxType : Nat)
    (extSize64 : Option Nat) : Option Mp4BoxSlice :=
  if Nat.ble (off + 8) bufLen then
    if Nat.beq size32 0 then
      some {
        boxType := boxType
        bodyStart := off + 8
        bodyLen := bufLen - (off + 8)
        nextOff := bufLen
      }
    else if Nat.beq size32 1 then
      match extSize64 with
      | none => none
      | some sz64 =>
        if Nat.ble (off + 16) bufLen && Nat.ble 16 sz64 &&
           Nat.ble sz64 (bufLen - off) then
          some {
            boxType := boxType
            bodyStart := off + 16
            bodyLen := sz64 - 16
            nextOff := off + sz64
          }
        else
          none
    else
      if Nat.ble 8 size32 && Nat.ble size32 (bufLen - off) then
        some {
          boxType := boxType
          bodyStart := off + 8
          bodyLen := size32 - 8
          nextOff := off + size32
        }
      else
        none
  else
    none

/-- Every accepted MP4 box header guarantees exact slice confinement
(`bodyStart + bodyLen = nextOff ≤ bufLen`) and strict forward progress by at
least 8 bytes (`off + 8 ≤ nextOff`). -/
theorem parseMp4BoxHeader_sound {bufLen off size32 boxType : Nat}
    {extSize64 : Option Nat} {box : Mp4BoxSlice}
    (h : parseMp4BoxHeader bufLen off size32 boxType extSize64 = some box) :
    off + 8 ≤ box.bodyStart ∧
    box.bodyStart + box.bodyLen = box.nextOff ∧
    off + 8 ≤ box.nextOff ∧
    box.nextOff ≤ bufLen := by
  unfold parseMp4BoxHeader at h
  cases h8 : Nat.ble (off + 8) bufLen with
  | false => rw [h8] at h; nomatch h
  | true =>
    rw [h8] at h
    have hOff8 : off + 8 ≤ bufLen := (ble_true_iff_le _ _).mp h8
    cases h0 : Nat.beq size32 0 with
    | true =>
      rw [h0] at h
      injection h with hEq
      subst hEq
      refine ⟨Nat.le_refl _, Nat.add_sub_of_le hOff8, hOff8, Nat.le_refl _⟩
    | false =>
      rw [h0] at h
      cases h1 : Nat.beq size32 1 with
      | true =>
        rw [h1] at h
        cases extSize64 with
        | none => nomatch h
        | some sz64 =>
          dsimp only at h
          cases hc : (Nat.ble (off + 16) bufLen && Nat.ble 16 sz64 &&
              Nat.ble sz64 (bufLen - off)) with
          | false => rw [hc] at h; nomatch h
          | true =>
            rw [hc] at h
            injection h with hEq
            subst hEq
            have hA := bool_and_left hc
            have hSzBuf : sz64 ≤ bufLen - off :=
              (ble_true_iff_le _ _).mp (bool_and_right hc)
            have h16Sz : 16 ≤ sz64 :=
              (ble_true_iff_le _ _).mp (bool_and_right hA)
            have hOff16 : off + 8 ≤ off + 16 :=
              Nat.add_le_add_left (by decide) off
            have hSum : off + 16 + (sz64 - 16) = off + sz64 := by
              rw [Nat.add_assoc, Nat.add_sub_of_le h16Sz]
            have hNextGe : off + 8 ≤ off + sz64 :=
              Nat.le_trans hOff16 (Nat.add_le_add_left h16Sz off)
            have hOffLe : off ≤ bufLen :=
              Nat.le_trans (Nat.le_add_right off 8) hOff8
            have hNextLe : off + sz64 ≤ bufLen := by
              have := Nat.add_le_add_left hSzBuf off
              rw [Nat.add_sub_of_le hOffLe] at this
              exact this
            exact ⟨hOff16, hSum, hNextGe, hNextLe⟩
      | false =>
        rw [h1] at h
        cases hc : (Nat.ble 8 size32 && Nat.ble size32 (bufLen - off)) with
        | false => rw [hc] at h; nomatch h
        | true =>
          rw [hc] at h
          injection h with hEq
          subst hEq
          have h8Sz : 8 ≤ size32 := (ble_true_iff_le _ _).mp (bool_and_left hc)
          have hSzBuf : size32 ≤ bufLen - off :=
            (ble_true_iff_le _ _).mp (bool_and_right hc)
          have hSum : off + 8 + (size32 - 8) = off + size32 := by
            rw [Nat.add_assoc, Nat.add_sub_of_le h8Sz]
          have hOffLe : off ≤ bufLen :=
            Nat.le_trans (Nat.le_add_right off 8) hOff8
          have hNextLe : off + size32 ≤ bufLen := by
            have := Nat.add_le_add_left hSzBuf off
            rw [Nat.add_sub_of_le hOffLe] at this
            exact this
          exact ⟨Nat.le_refl _, hSum, Nat.add_le_add_left h8Sz off, hNextLe⟩

/-- Strict decrease of remaining buffer bytes by at least 8 bytes per box
(directly establishing loop termination in `≤ (bufLen - off) / 8` boxes). -/
theorem parseMp4BoxHeader_rem_decrease {bufLen off size32 boxType : Nat}
    {extSize64 : Option Nat} {box : Mp4BoxSlice}
    (h : parseMp4BoxHeader bufLen off size32 boxType extSize64 = some box) :
    (bufLen - box.nextOff) + 8 ≤ bufLen - off := by
  have hs := parseMp4BoxHeader_sound h
  have h1 : box.nextOff + (bufLen - box.nextOff) = bufLen :=
    Nat.add_sub_of_le hs.2.2.2
  have h2 : off + 8 + (bufLen - box.nextOff) ≤ bufLen := by
    have := Nat.add_le_add_right hs.2.2.1 (bufLen - box.nextOff)
    rw [h1] at this
    exact this
  have h3 : off + ((bufLen - box.nextOff) + 8) ≤ bufLen := by
    rw [Nat.add_comm (bufLen - box.nextOff) 8, ← Nat.add_assoc]
    exact h2
  have h4 : off + ((bufLen - box.nextOff) + 8) ≤ off + (bufLen - off) := by
    have hoff : off ≤ bufLen :=
      Nat.le_trans (Nat.le_add_right off 8) (Nat.le_trans hs.2.2.1 hs.2.2.2)
    rw [Nat.add_sub_of_le hoff]
    exact h3
  exact Nat.le_of_add_le_add_left h4

/-! ## Part 2: AV1 (`rav1d`) OBU Header Bit-Lens & Framing -/

/-- Decoded AV1 §5.3.2 OBU header byte fields. -/
structure ObuHeader where
  /-- Bit 7: `obu_forbidden_bit` (must be `false` in valid AV1 bitstreams). -/
  forbidden : Bool
  /-- Bits 6..3: 4-bit `obu_type` (`0..15`). -/
  obuType : Nat
  /-- Bit 2: `obu_extension_flag`. -/
  hasExtension : Bool
  /-- Bit 1: `obu_has_size_field`. -/
  hasSizeField : Bool
  /-- Bit 0: `obu_reserved_1bit`. -/
  reserved : Bool

/-- Unpack an AV1 OBU header byte into `ObuHeader` via `bitSlice`. -/
@[expose] def unpackObuHeader (b : Nat) : ObuHeader :=
  { forbidden := Nat.beq (bitSlice b 7 1) 1
    obuType := bitSlice b 3 4
    hasExtension := Nat.beq (bitSlice b 2 1) 1
    hasSizeField := Nat.beq (bitSlice b 1 1) 1
    reserved := Nat.beq (bitSlice b 0 1) 1 }

/-- Pack an `ObuHeader` back into an 8-bit unsigned byte. -/
@[expose] def packObuHeader (h : ObuHeader) : Nat :=
  (if h.forbidden then 128 else 0) +
  h.obuType * 8 +
  (if h.hasExtension then 4 else 0) +
  (if h.hasSizeField then 2 else 0) +
  (if h.reserved then 1 else 0)

/-- `obuType` unpacked from any byte is strictly below `16`. -/
theorem unpackObuHeader_type_lt (b : Nat) :
    (unpackObuHeader b).obuType < 16 :=
  bitSlice_lt b 3 4

/-- `packObuHeader` of any header with `obuType < 16` fits in a byte `< 256`. -/
theorem packObuHeader_lt (h : ObuHeader) (ht : h.obuType < 16) :
    packObuHeader h < 256 := by
  unfold packObuHeader
  have hlow : (if h.hasExtension then 4 else 0) +
      (if h.hasSizeField then 2 else 0) +
      (if h.reserved then 1 else 0) < 8 := by
    cases h.hasExtension <;> cases h.hasSizeField <;> cases h.reserved <;>
      decide
  have hmid : h.obuType * 8 +
      ((if h.hasExtension then 4 else 0) +
       (if h.hasSizeField then 2 else 0) +
       (if h.reserved then 1 else 0)) < 128 := by
    have h1 : h.obuType * 8 + ((if h.hasExtension then 4 else 0) +
        (if h.hasSizeField then 2 else 0) +
        (if h.reserved then 1 else 0)) < h.obuType * 8 + 8 :=
      Nat.add_lt_add_left hlow _
    have h2 : h.obuType * 8 + 8 = (h.obuType + 1) * 8 := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right 8 ht)
  have hre : (if h.forbidden then 128 else 0) + h.obuType * 8 +
      (if h.hasExtension then 4 else 0) + (if h.hasSizeField then 2 else 0) +
      (if h.reserved then 1 else 0) =
      (if h.forbidden then 128 else 0) +
      (h.obuType * 8 +
        (((if h.hasExtension then 4 else 0) +
          (if h.hasSizeField then 2 else 0)) +
         (if h.reserved then 1 else 0))) := by
    rw [Nat.add_assoc (if h.forbidden then 128 else 0),
        Nat.add_assoc (if h.forbidden then 128 else 0),
        Nat.add_assoc (if h.forbidden then 128 else 0),
        Nat.add_assoc (h.obuType * 8),
        Nat.add_assoc (h.obuType * 8)]
  rw [hre]
  cases h.forbidden with
  | false =>
    change 0 + (h.obuType * 8 + _) < 256
    rw [Nat.zero_add]
    exact Nat.lt_trans hmid (by decide)
  | true =>
    change 128 + (h.obuType * 8 + _) < 128 + 128
    exact Nat.add_lt_add_left hmid 128

private theorem bool_bit_val_eq (x : Nat) (hx : x < 2) :
    (if Nat.beq x 1 then 1 else 0) = x := by
  cases x with
  | zero => rfl
  | succ x' =>
    cases x' with
    | zero => rfl
    | succ x'' =>
      exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 x'') hx)

/-- Exact bit-level `GetPut` round-trip: re-packing `unpackObuHeader b`
recovers every valid byte `b < 256`. -/
theorem packObuHeader_unpack (b : Nat) (hb : b < 256) :
    packObuHeader (unpackObuHeader b) = b := by
  have hfull : bitSlice b 0 8 = b := bitSlice_full_of_lt hb
  have hs1 : bitSlice b 0 8 = bitSlice b 0 1 + 2 * bitSlice b 1 7 :=
    bitSlice_adjacent b 0 1 7
  have hs2 : bitSlice b 1 7 = bitSlice b 1 1 + 2 * bitSlice b 2 6 :=
    bitSlice_adjacent b 1 1 6
  have hs3 : bitSlice b 2 6 = bitSlice b 2 1 + 2 * bitSlice b 3 5 :=
    bitSlice_adjacent b 2 1 5
  have hs4 : bitSlice b 3 5 = bitSlice b 3 4 + 16 * bitSlice b 7 1 :=
    bitSlice_adjacent b 3 4 1
  rw [hs1, hs2, hs3, hs4] at hfull
  have hb0 := bool_bit_val_eq (bitSlice b 0 1) (bitSlice_lt b 0 1)
  have hb1 := bool_bit_val_eq (bitSlice b 1 1) (bitSlice_lt b 1 1)
  have hb2 := bool_bit_val_eq (bitSlice b 2 1) (bitSlice_lt b 2 1)
  have hb7 := bool_bit_val_eq (bitSlice b 7 1) (bitSlice_lt b 7 1)
  have hsc : ∀ (c : Bool) (k : Nat),
      (if c then k else 0) = k * (if c then 1 else 0) := by
    intro c k; cases c <;> simp
  have hrearr : ∀ x0 x1 x2 x3 x7 : Nat,
      128 * x7 + x3 * 8 + 4 * x2 + 2 * x1 + x0 =
        x0 + 2 * (x1 + 2 * (x2 + 2 * (x3 + 16 * x7))) := by
    intro x0 x1 x2 x3 x7
    rw [Nat.mul_add 2 x3 (16 * x7), ← Nat.mul_assoc 2 16 x7]
    rw [Nat.mul_add 2 x2 _, Nat.mul_add 2 (2 * x3) _,
        ← Nat.mul_assoc 2 2 x3, ← Nat.mul_assoc 2 32 x7]
    rw [Nat.mul_add 2 x1 _, Nat.mul_add 2 (2 * x2) _, Nat.mul_add 2 (4 * x3) _,
        ← Nat.mul_assoc 2 2 x2, ← Nat.mul_assoc 2 4 x3, ← Nat.mul_assoc 2 64 x7]
    rw [Nat.mul_comm x3 8]
    rw [Nat.add_comm (128 * x7) (8 * x3)]
    rw [Nat.add_comm (8 * x3 + 128 * x7) (4 * x2)]
    rw [Nat.add_comm (4 * x2 + (8 * x3 + 128 * x7)) (2 * x1)]
    rw [Nat.add_comm (2 * x1 + (4 * x2 + (8 * x3 + 128 * x7))) x0]
  unfold packObuHeader unpackObuHeader
  dsimp only
  rw [hsc _ 128, hsc _ 4, hsc _ 2, hb0, hb1, hb2, hb7]
  exact (hrearr _ _ _ _ _).trans hfull

/-- Framed AV1 OBU unit decoded from a byte list, returning
`(header, optionalExtByte, payloadBytes, remainingBytes)`. Rejects forbidden
bit `= true`, truncated extension byte, truncated LEB128 size, or payload size
exceeding remaining bytes. -/
@[expose] def parseObuUnit (bs : List Nat) :
    Option (ObuHeader × Option Nat × List Nat × List Nat) :=
  match bs with
  | [] => none
  | hdrByte :: rest1 =>
    let hdr := unpackObuHeader hdrByte
    if hdr.forbidden then
      none
    else
      let afterExt : Option (Option Nat × List Nat) :=
        if hdr.hasExtension then
          match rest1 with
          | [] => none
          | extB :: rest2 => some (some extB, rest2)
        else
          some (none, rest1)
      match afterExt with
      | none => none
      | some (extOpt, restAfterExt) =>
        if hdr.hasSizeField then
          match decodeLeb128 restAfterExt with
          | none => none
          | some (sz, afterSz) =>
            if Nat.ble sz afterSz.length then
              some (hdr, extOpt, listTake sz afterSz, listDrop sz afterSz)
            else
              none
        else
          some (hdr, extOpt, restAfterExt, [])

/-- Every successfully parsed AV1 OBU unit strictly consumes at least 1 byte
(`rem.length < bs.length`, guaranteeing OBU-stream demuxer termination) and
guarantees `hdr.forbidden = false`. -/
theorem parseObuUnit_progress {bs payload rem : List Nat}
    {hdr : ObuHeader} {extOpt : Option Nat}
    (h : parseObuUnit bs = some (hdr, extOpt, payload, rem)) :
    hdr.forbidden = false ∧ rem.length < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons b rest1 =>
    unfold parseObuUnit at h
    dsimp only at h
    cases hf : (unpackObuHeader b).forbidden with
    | true => rw [hf] at h; nomatch h
    | false =>
      rw [hf] at h
      have hRest : ∀ (e : Option Nat) (r : List Nat),
          (if (unpackObuHeader b).hasExtension then
            match rest1 with
            | [] => none
            | extB :: rest2 => some (some extB, rest2)
          else some (none, rest1)) = some (e, r) →
          r.length ≤ rest1.length := by
        intro e r he
        cases hExt : (unpackObuHeader b).hasExtension with
        | false =>
          rw [hExt] at he
          injection he with hp
          injection hp with _ hr
          rw [hr]
          exact Nat.le_refl _
        | true =>
          rw [hExt] at he
          cases rest1 with
          | nil => nomatch he
          | cons eb r2 =>
            injection he with hp
            injection hp with _ hr
            rw [hr]
            exact Nat.le_succ r.length
      cases hae : (if (unpackObuHeader b).hasExtension then
            match rest1 with
            | [] => none
            | extB :: rest2 => some (some extB, rest2)
          else some (none, rest1)) with
      | none => rw [hae] at h; nomatch h
      | some p =>
        rw [hae] at h
        cases p with
        | mk eOpt restAE =>
          have hLe1 : restAE.length ≤ rest1.length := hRest eOpt restAE hae
          change (if (unpackObuHeader b).hasSizeField then
            match decodeLeb128 restAE with
            | none => none
            | some (sz, afterSz) =>
              if Nat.ble sz afterSz.length then
                some (unpackObuHeader b, eOpt,
                  listTake sz afterSz, listDrop sz afterSz)
              else none
          else some (unpackObuHeader b, eOpt, restAE, [])) =
            some (hdr, extOpt, payload, rem) at h
          cases hsz : (unpackObuHeader b).hasSizeField with
          | false =>
            rw [hsz] at h
            injection h with hp
            injection hp with hhdr htail
            injection htail with _ htail2
            injection htail2 with _ hrem
            rw [← hhdr, ← hrem]
            exact ⟨hf, Nat.zero_lt_succ rest1.length⟩
          | true =>
            rw [hsz] at h
            change (match decodeLeb128 restAE with
              | none => none
              | some (sz, afterSz) =>
                if Nat.ble sz afterSz.length then
                  some (unpackObuHeader b, eOpt,
                    listTake sz afterSz, listDrop sz afterSz)
                else none) = some (hdr, extOpt, payload, rem) at h
            cases hleb : decodeLeb128 restAE with
            | none => rw [hleb] at h; nomatch h
            | some q =>
              rw [hleb] at h
              cases q with
              | mk sz afterSz =>
                change (if Nat.ble sz afterSz.length then
                  some (unpackObuHeader b, eOpt,
                    listTake sz afterSz, listDrop sz afterSz)
                else none) = some (hdr, extOpt, payload, rem) at h
                cases hble : Nat.ble sz afterSz.length with
                | false => rw [hble] at h; nomatch h
                | true =>
                  rw [hble] at h
                  injection h with hp
                  injection hp with hhdr htail
                  injection htail with _ htail2
                  injection htail2 with _ hrem
                  have hLebLen : ∀ (k : Nat) (xs tail : List Nat) (v : Nat),
                      decodeLeb128Aux k xs = some (v, tail) →
                      tail.length < xs.length := by
                    intro k
                    induction k with
                    | zero => intro xs tail v hd; nomatch hd
                    | succ k ih =>
                      intro xs tail v hd
                      cases xs with
                      | nil => nomatch hd
                      | cons x xs' =>
                        rw [decodeLeb128Aux_succ_cons] at hd
                        cases hb : Nat.blt x 128 with
                        | true =>
                          rw [hb] at hd
                          injection hd with hp'
                          injection hp' with _ htl
                          rw [htl]
                          exact Nat.lt_succ_self tail.length
                        | false =>
                          rw [hb] at hd
                          change (match decodeLeb128Aux k xs' with
                            | none => none
                            | some (hi, tl) =>
                              some (HMod.hMod x 128 + 128 * hi, tl)) =
                            some (v, tail) at hd
                          cases hr : decodeLeb128Aux k xs' with
                          | none => rw [hr] at hd; nomatch hd
                          | some q' =>
                            rw [hr] at hd
                            injection hd with hp'
                            injection hp' with _ htl
                            rw [← htl]
                            exact Nat.lt_trans (ih xs' q'.2 q'.1 hr)
                              (Nat.lt_succ_self xs'.length)
                  have hqLt : afterSz.length < restAE.length :=
                    hLebLen 8 restAE afterSz sz hleb
                  have hDropLe :
                      (listDrop sz afterSz).length ≤ afterSz.length := by
                    rw [listDrop_length]
                    exact Nat.sub_le _ _
                  rw [← hhdr, ← hrem]
                  refine ⟨hf, ?_⟩
                  have h1 := Nat.lt_of_le_of_lt hDropLe hqLt
                  have h2 := Nat.lt_of_lt_of_le h1 hLe1
                  exact Nat.lt_trans h2 (Nat.lt_succ_self rest1.length)

/-! ## Part 3: H.264 §7.4.2.1.1 SPS Frame-Dimension & Chroma-Crop Spec -/

/-- H.264 Table 6-1 `chroma_format_idc` horizontal subsampling factor
`SubWidthC` (1 for 4:0:0/4:4:4, 2 for 4:2:0/4:2:2). -/
@[expose] def h264SubWidthC (chromaFormatIdc : Nat) : Nat :=
  if Nat.beq chromaFormatIdc 1 || Nat.beq chromaFormatIdc 2 then 2 else 1

/-- H.264 Table 6-1 `chroma_format_idc` vertical subsampling factor `SubHeightC`
(2 for 4:2:0, 1 otherwise). -/
@[expose] def h264SubHeightC (chromaFormatIdc : Nat) : Nat :=
  if Nat.beq chromaFormatIdc 1 then 2 else 1

/-- H.264 SPS frame-dimension and crop parameter bundle. -/
structure SpsDimParams where
  chromaFormatIdc : Nat
  bitDepthLumaMinus8 : Nat
  bitDepthChromaMinus8 : Nat
  picWidthInMbsMinus1 : Nat
  picHeightInMapUnitsMinus1 : Nat
  frameMbsOnly : Bool
  cropLeft : Nat
  cropRight : Nat
  cropTop : Nat
  cropBottom : Nat

/-- Coded luma width in samples (`16 * (picWidthInMbsMinus1 + 1)`). -/
@[expose] def SpsDimParams.codedWidth (s : SpsDimParams) : Nat :=
  16 * (s.picWidthInMbsMinus1 + 1)

/-- Coded luma height in samples
(`16 * (2 - frameMbsOnly) * (picHeightInMapUnitsMinus1 + 1)`). -/
@[expose] def SpsDimParams.codedHeight (s : SpsDimParams) : Nat :=
  (if s.frameMbsOnly then 16 else 32) * (s.picHeightInMapUnitsMinus1 + 1)

/-- Horizontal crop unit `CropUnitX = SubWidthC`. -/
@[expose] def SpsDimParams.cropUnitX (s : SpsDimParams) : Nat :=
  h264SubWidthC s.chromaFormatIdc

/-- Vertical crop unit `CropUnitY = SubHeightC * (2 - frameMbsOnly)`. -/
@[expose] def SpsDimParams.cropUnitY (s : SpsDimParams) : Nat :=
  h264SubHeightC s.chromaFormatIdc * (if s.frameMbsOnly then 1 else 2)

/-- Complete CVE-hardened H.264 SPS dimension & crop validator matching
`validate_h264_sps_frame_dims` (prevents CVE-2012-0851 invalid chroma format,
CVE-2013-2277 excessive bit depth, crop underflow, and 32-bit pixel-count
overflow for up to 16K frames). -/
@[expose] def spsDimsValid (s : SpsDimParams) : Bool :=
  Nat.ble s.chromaFormatIdc 3 &&
  Nat.ble s.bitDepthLumaMinus8 6 &&
  Nat.ble s.bitDepthChromaMinus8 6 &&
  Nat.ble s.picWidthInMbsMinus1 1023 &&
  Nat.ble s.picHeightInMapUnitsMinus1 511 &&
  Nat.blt ((s.cropLeft + s.cropRight) * s.cropUnitX) s.codedWidth &&
  Nat.blt ((s.cropTop + s.cropBottom) * s.cropUnitY) s.codedHeight

/-- Every validated H.264 SPS satisfies: valid `chromaFormatIdc ≤ 3`, valid
luma/chroma bit depths `≤ 14`, strictly positive cropped width and height, and
32-bit overflow-free coded sample count `codedWidth * codedHeight < 2^32`. -/
theorem spsDimsValid_sound {s : SpsDimParams} (h : spsDimsValid s = true) :
    s.chromaFormatIdc ≤ 3 ∧
    8 + s.bitDepthLumaMinus8 ≤ 14 ∧
    8 + s.bitDepthChromaMinus8 ≤ 14 ∧
    0 < s.codedWidth - (s.cropLeft + s.cropRight) * s.cropUnitX ∧
    0 < s.codedHeight - (s.cropTop + s.cropBottom) * s.cropUnitY ∧
    s.codedWidth * s.codedHeight < HPow.hPow (2 : Nat) 32 := by
  unfold spsDimsValid at h
  have h6 := bool_and_left h
  have hCropH : (s.cropTop + s.cropBottom) * s.cropUnitY < s.codedHeight :=
    (blt_true_iff_lt _ _).mp (bool_and_right h)
  have h5 := bool_and_left h6
  have hCropW : (s.cropLeft + s.cropRight) * s.cropUnitX < s.codedWidth :=
    (blt_true_iff_lt _ _).mp (bool_and_right h6)
  have h4 := bool_and_left h5
  have hHmb : s.picHeightInMapUnitsMinus1 ≤ 511 :=
    (ble_true_iff_le _ _).mp (bool_and_right h5)
  have h3 := bool_and_left h4
  have hWmb : s.picWidthInMbsMinus1 ≤ 1023 :=
    (ble_true_iff_le _ _).mp (bool_and_right h4)
  have h2 := bool_and_left h3
  have hBdC : s.bitDepthChromaMinus8 ≤ 6 :=
    (ble_true_iff_le _ _).mp (bool_and_right h3)
  have hChroma : s.chromaFormatIdc ≤ 3 :=
    (ble_true_iff_le _ _).mp (bool_and_left h2)
  have hBdL : s.bitDepthLumaMinus8 ≤ 6 :=
    (ble_true_iff_le _ _).mp (bool_and_right h2)
  have hWle : s.codedWidth ≤ 16384 := by
    unfold SpsDimParams.codedWidth
    exact Nat.mul_le_mul_left 16 (Nat.succ_le_succ hWmb)
  have hHle : s.codedHeight ≤ 16384 := by
    unfold SpsDimParams.codedHeight
    cases s.frameMbsOnly with
    | true =>
      have h1 := Nat.mul_le_mul_left 16 (Nat.succ_le_succ hHmb)
      exact Nat.le_trans h1 (by decide)
    | false =>
      exact Nat.mul_le_mul_left 32 (Nat.succ_le_succ hHmb)
  have hProd : s.codedWidth * s.codedHeight < HPow.hPow (2 : Nat) 32 := by
    have hm := Nat.mul_le_mul hWle hHle
    exact Nat.lt_of_le_of_lt hm (by decide)
  exact ⟨hChroma,
         Nat.add_le_add_left hBdL 8,
         Nat.add_le_add_left hBdC 8,
         Nat.sub_pos_of_lt hCropW,
         Nat.sub_pos_of_lt hCropH,
         hProd⟩

end Anneal.MediaBits.SyntaxLens

end
