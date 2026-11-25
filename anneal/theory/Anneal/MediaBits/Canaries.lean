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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Data.Int.Basic
public import Anneal.MediaBits.Rbsp
public import Anneal.MediaBits.BitCursor

public section

/-!
# Concrete Positive & Negative Canaries for `Anneal.MediaBits`

End-to-end positive witnesses and single-cause counterexamples exercising
`Anneal.MediaBits.Rbsp` and `Anneal.MediaBits.BitCursor`:

1. **Canary 1 (`canary1_rbsp_bijection_tight_bound_and_malleability`):**
   Exercises `rbspUnescapeStrict_escape`, `rbspEscape_of_unescapeStrict_some`,
   `rbspEscape_len_ge`, `rbspEscape_two_mul_len_le`, `rbspEscape_len_le_div2`,
   the tight `⌊3n/2⌋` witness `[0, 0, 0, 0, 0] ↦ [0, 0, 3, 0, 0, 3, 0]`
   (length `7`), the §7.4.1 end-of-input `cabac_zero_word` rule
   (`[0, 0] ↦ [0, 0, 3]`, strict acceptance of trailing `[0, 0, 3]` as
   `[0, 0]`, and rejection of a trailing unescaped `[0, 0]`), strict
   rejection of forbidden `[0, 0, 0]`, `[0, 0, 1]`, `[0, 0, 2]`, and
   non-canonical `[0, 0, 3, 4]`, plus `rbspUnescapeLenient_breaks_getPut`.
2. **Canary 2 (`canary2_byteBit_packing_and_readWriteBits`):**
   Exercises `bytesToBits_len`, `bitsToBytesN_bytesToBits`,
   `bytesToBits_of_bitsToBytesN`, `readBits_writeBits`, and
   `writeBits_of_readBits` on H.264 NAL bytes `[0x67, 0x42, 0x00, 0x1E]`
   (including bit-field packing `0 || 3 || 7 = 0x67` for an SPS NAL header),
   plus truncated-stream rejections.
3. **Canary 3 (`canary3_expGolomb_ue_se_bijection_and_rejections`):**
   Exercises `decodeUe_encodeUe`, `encodeUe_of_decodeUe`, `decodeSe_encodeSe`,
   `encodeSe_of_decodeSe`, exact H.264 Table 9-1 / 9-3 bit encodings, and
   rejection of all-zero and truncated Exp-Golomb bit streams.
4. **Canary 4 (`canary4_dualContext_pps_transcode_vs_singleContext_bug`):**
   Concrete H.264 `PPS` + `P_SLICE` 3-unit stream transcoder proving
   `IndexedPutGet` and `IndexedGetPut` on `ppsCodec`, positive
   `dualContext_transcodeStream_sound` preserving effective slice QP across
   `weightedPred` header rewriting, and negative single-context parse failure
   when mutating `PPS` overwrites the parser context in place.
5. **Canary 5 (`canary5_layered_ebsp_rbsp_bits_and_expGolomb_pipeline`):**
   Composes `rbspEscape` / `rbspUnescapeStrict`, `bytesToBits` / `bitsToBytesN`,
   and `readBits` / `decodeUe` / `decodeSe` across a concrete EBSP NAL unit
   containing an emulation-prevention `0x00 0x00 0x03` byte.
-/

namespace Anneal.MediaBits

/-! ## Canary 1: Strict `0x000003` RBSP Bijection, Tight Bound & Malleability -/

/-- Canary 1 (`[propext]` only): verifies `rbspUnescapeStrict_escape`,
`rbspEscape_of_unescapeStrict_some`, tight `⌊3n/2⌋` expansion on five zeros,
the end-of-input `cabac_zero_word` escape (`[0, 0] ↔ [0, 0, 3]`), strict
rejection of forbidden, trailing-unescaped, and malleable sequences, and
`rbspUnescapeLenient_breaks_getPut`. -/
theorem canary1_rbsp_bijection_tight_bound_and_malleability :
    let pTight := [0, 0, 0, 0, 0]
    let eTight := [0, 0, 3, 0, 0, 3, 0]
    rbspEscape pTight = eTight ∧
    rbspUnescapeStrict eTight = some pTight ∧
    rbspEscape [0, 0, 4] = [0, 0, 4] ∧
    pTight.length ≤ (rbspEscape pTight).length ∧
    (rbspEscape pTight).length ≤ Nat.div (3 * pTight.length) 2 ∧
    (rbspEscape pTight).length = Nat.div (3 * pTight.length) 2 ∧
    rbspUnescapeStrict [0, 0, 0] = none ∧
    rbspUnescapeStrict [0, 0, 1] = none ∧
    rbspUnescapeStrict [0, 0, 2] = none ∧
    rbspUnescapeStrict [0, 0, 3] = some [0, 0] ∧
    rbspEscape [0, 0] = [0, 0, 3] ∧
    rbspUnescapeStrict [0, 0] = none ∧
    rbspUnescapeStrict [0, 0, 3, 4] = none ∧
    (rbspUnescapeLenient [0, 0, 3, 4] = [0, 0, 4] ∧
      rbspEscape (rbspUnescapeLenient [0, 0, 3, 4]) ≠ [0, 0, 3, 4]) := by
  intro pTight eTight
  have hLenient := rbspUnescapeLenient_breaks_getPut
  have hDiv15 : Nat.div 15 2 = 7 :=
    Nat.le_antisymm
      (Nat.le_of_lt_succ
        ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).mpr
          (Nat.lt_of_sub_eq_succ (n := 15) (m := 16) rfl)))
      ((Nat.le_div_iff_mul_le (Nat.zero_lt_succ 1)).mpr
        (Nat.le_of_lt (Nat.lt_of_sub_eq_succ (n := 14) (m := 15) rfl)))
  exact ⟨rfl, rbspUnescapeStrict_escape pTight, rfl,
    rbspEscape_len_ge pTight, rbspEscape_len_le_div2 pTight, hDiv15.symm,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨hLenient.2.1, hLenient.2.2.2⟩⟩

/-! ## Canary 2: Byte-Bit Packing & Fixed-Width `readBits` / `writeBits` -/

private theorem natLt256_of_sub_eq_succ {n k : Nat} (h : 256 - n = k + 1) :
    n < 256 :=
  Nat.lt_of_sub_eq_succ h

/-- Canary 2 (`[propext]` only): verifies `bytesToBits_len`,
`bitsToBytesN_bytesToBits`, `bytesToBits_of_bitsToBytesN`, H.264 SPS NAL header
bit packing (`0 || 3 || 7 = 0x67`), fixed-width `PutGet` + raw-bitlist `GetPut`
round-trips with trailing bits, and truncated-stream rejection. -/
theorem canary2_byteBit_packing_and_readWriteBits :
    let nalBytes := [0x67, 0x42, 0x00, 0x1E]
    let trail := [true, false]
    let raw5 := [false, false, true, true, true, true, false]
    let rawByte := [false, true, true, false, false, true, true, true, true]
    (bytesToBits nalBytes).length = 32 ∧
    bitsToBytesN 4 (bytesToBits nalBytes ++ trail) = some (nalBytes, trail) ∧
    (bytesToBits [0x67] ++ [true] = rawByte ∧ AllBytesLt256 [0x67]) ∧
    (writeBits 1 0 ++ writeBits 2 3 ++ writeBits 5 7 = writeBits 8 0x67) ∧
    readBits 5 (writeBits 5 7 ++ trail) = some (7, trail) ∧
    writeBits 5 7 ++ trail = raw5 ∧
    readBits 8 [true, false, true] = none ∧
    bitsToBytesN 2 (bytesToBits [0x67]) = none := by
  intro nalBytes trail raw5 rawByte
  have hAll : AllBytesLt256 nalBytes :=
    ⟨natLt256_of_sub_eq_succ (n := 0x67) (k := 152) rfl,
     natLt256_of_sub_eq_succ (n := 0x42) (k := 189) rfl,
     natLt256_of_sub_eq_succ (n := 0x00) (k := 255) rfl,
     natLt256_of_sub_eq_succ (n := 0x1E) (k := 225) rfl,
     True.intro⟩
  have hUnpack := bitsToBytesN_bytesToBits nalBytes trail hAll
  have hUnpackRaw : bitsToBytesN 1 rawByte = some ([0x67], [true]) := rfl
  have hRepackRaw :=
    bytesToBits_of_bitsToBytesN 1 rawByte [0x67] [true] hUnpackRaw
  have hRead5 :=
    readBits_writeBits 5 7 trail (Nat.lt_of_sub_eq_succ (n := 7) (m := 32) rfl)
  have hRead5Raw : readBits 5 raw5 = some (7, trail) := rfl
  exact ⟨bytesToBits_len nalBytes, hUnpack, ⟨hRepackRaw.1, hRepackRaw.2.2⟩, rfl,
    hRead5, writeBits_of_readBits 5 raw5 7 trail hRead5Raw,
    rfl, rfl⟩

/-! ## Canary 3: Exp-Golomb `ue(v)` / `se(v)` Bijection & Rejections -/

/-- Canary 3 (`[propext]` only): verifies `decodeUe_encodeUe`,
`encodeUe_of_decodeUe`, `decodeSe_encodeSe`, `encodeSe_of_decodeSe` on concrete
raw bitstreams, exact H.264 Table 9-1 / 9-3 bit encodings, and rejection of
malformed prefixes. -/
theorem canary3_expGolomb_ue_se_bijection_and_rejections :
    let trail := [true, true]
    let rawUe7 := [false, false, false, true, false, false, false, true, true]
    let rawSeNeg2 := [false, false, true, false, true, true, true]
    encodeUe 0 = [true] ∧
    encodeUe 4 = [false, false, true, false, true] ∧
    encodeSe (Int.negSucc 1) = [false, false, true, false, true] ∧
    decodeUe (encodeUe 7 ++ trail) = some (7, trail) ∧
    encodeUe 7 ++ trail = rawUe7 ∧
    decodeSe (encodeSe (Int.negSucc 2) ++ trail) = some (Int.negSucc 2, trail) ∧
    encodeSe (Int.negSucc 1) ++ trail = rawSeNeg2 ∧
    decodeSe (encodeSe (Int.ofNat 3) ++ trail) = some (Int.ofNat 3, trail) ∧
    decodeUe [false, false, false] = none ∧
    decodeUe [false, false, true, false] = none ∧
    decodeSe [false, false] = none := by
  intro trail rawUe7 rawSeNeg2
  have hUe7 := decodeUe_encodeUe 7 trail
  have hRawUe7 : decodeUe rawUe7 = some (7, trail) := rfl
  have hRawSeNeg2 : decodeSe rawSeNeg2 = some (Int.negSucc 1, trail) := rfl
  exact ⟨rfl, rfl, rfl, hUe7, encodeUe_of_decodeUe hRawUe7,
    decodeSe_encodeSe (Int.negSucc 2) trail,
    encodeSe_of_decodeSe hRawSeNeg2,
    decodeSe_encodeSe (Int.ofNat 3) trail,
    rfl, rfl, rfl⟩

/-! ## Canary 4: Dual-Context `PPS` + `P_SLICE` vs. Single-Context Bug -/

/-- H.264-style `PPS` parameter-set context tracking `weightedPred` flag and
`initQp`. -/
structure PpsCtx where
  weightedPred : Bool
  initQp : Int

/-- High-level syntax unit AST (`pps` header or `pSlice` header). -/
inductive MediaUnit where
  | pps (wp : Bool) (initQp : Int)
  | pSlice (qpDelta : Int) (weightTag : Option Nat)

/-- Wire representation distinguishing unweighted vs. weighted slice syntax. -/
inductive MediaWire where
  | wPps (wp : Bool) (initQp : Int)
  | wSliceNoWeight (qpDelta : Int)
  | wSliceWeighted (qpDelta : Int) (weightTag : Nat)

/-- Context-indexed H.264 `PPS` + `P_SLICE` codec: `wSliceNoWeight` parses
only when `ctx.weightedPred = false`; `wSliceWeighted` parses only when
`ctx.weightedPred = true`. -/
@[expose] def ppsCodec : IndexedCodec PpsCtx MediaUnit MediaWire where
  get := fun ctx wire =>
    match wire with
    | .wPps wp qp => some (⟨wp, qp⟩, .pps wp qp)
    | .wSliceNoWeight d =>
      match ctx.weightedPred with
      | false => some (ctx, .pSlice d none)
      | true => none
    | .wSliceWeighted d w =>
      match ctx.weightedPred with
      | true => some (ctx, .pSlice d (some w))
      | false => none
  put := fun ctx unit =>
    match unit with
    | .pps wp qp => some (⟨wp, qp⟩, .wPps wp qp)
    | .pSlice d none =>
      match ctx.weightedPred with
      | false => some (ctx, .wSliceNoWeight d)
      | true => none
    | .pSlice d (some w) =>
      match ctx.weightedPred with
      | true => some (ctx, .wSliceWeighted d w)
      | false => none

/-- `IndexedPutGet` law for `ppsCodec` (`[]` zero axioms). -/
theorem ppsCodec_putGet : IndexedPutGet ppsCodec := by
  intro ctx unit ctx' wire hPut
  cases unit with
  | pps wp qp =>
    dsimp only [ppsCodec] at hPut
    injection hPut with hPair
    injection hPair with hCtx hWire
    rw [← hCtx, ← hWire]
    rfl
  | pSlice d tag =>
    cases tag with
    | none =>
      dsimp only [ppsCodec] at hPut
      cases hWp : ctx.weightedPred with
      | true =>
        rw [hWp] at hPut
        nomatch hPut
      | false =>
        rw [hWp] at hPut
        injection hPut with hPair
        injection hPair with hCtx hWire
        rw [← hCtx, ← hWire]
        dsimp only [ppsCodec]
        rw [hWp]
    | some w =>
      dsimp only [ppsCodec] at hPut
      cases hWp : ctx.weightedPred with
      | false =>
        rw [hWp] at hPut
        nomatch hPut
      | true =>
        rw [hWp] at hPut
        injection hPut with hPair
        injection hPair with hCtx hWire
        rw [← hCtx, ← hWire]
        dsimp only [ppsCodec]
        rw [hWp]

/-- `IndexedGetPut` law for `ppsCodec` (`[]` zero axioms). -/
theorem ppsCodec_getPut : IndexedGetPut ppsCodec := by
  intro ctx wire ctx' unit hGet
  cases wire with
  | wPps wp qp =>
    dsimp only [ppsCodec] at hGet
    injection hGet with hPair
    injection hPair with hCtx hUnit
    rw [← hCtx, ← hUnit]
    rfl
  | wSliceNoWeight d =>
    dsimp only [ppsCodec] at hGet
    cases hWp : ctx.weightedPred with
    | true =>
      rw [hWp] at hGet
      nomatch hGet
    | false =>
      rw [hWp] at hGet
      injection hGet with hPair
      injection hPair with hCtx hUnit
      rw [← hCtx, ← hUnit]
      dsimp only [ppsCodec]
      rw [hWp]
  | wSliceWeighted d w =>
    dsimp only [ppsCodec] at hGet
    cases hWp : ctx.weightedPred with
    | false =>
      rw [hWp] at hGet
      nomatch hGet
    | true =>
      rw [hWp] at hGet
      injection hGet with hPair
      injection hPair with hCtx hUnit
      rw [← hCtx, ← hUnit]
      dsimp only [ppsCodec]
      rw [hWp]

/-- Dual-context `PPS` filter rewriting `PPS(wp, qp)` to `PPS(true, 0)` and
adjusting every subsequent `pSlice` by `qpDelta + (sIn.initQp - sOut.initQp)`
with `weightTag := some 0`. -/
@[expose] def ppsRewriteTranscoder :
    DualContextTranscoder PpsCtx PpsCtx MediaUnit MediaWire where
  inCodec := ppsCodec
  outCodec := ppsCodec
  rewrite := fun sIn sOut unit =>
    match unit with
    | .pps _ _ => some (.pps true 0)
    | .pSlice d _ => some (.pSlice (d + (sIn.initQp - sOut.initQp)) (some 0))

/-- Naive single-context stream filter that overwrites the single shared
context `cur` with the output serializer's post-state (`0` `._unsafe_rec`). -/
@[expose] def naiveSingleContextStream
    (t : DualContextTranscoder PpsCtx PpsCtx MediaUnit MediaWire)
    (ctx : PpsCtx) (pkts : List MediaWire) : Option (PpsCtx × List MediaWire) :=
  List.foldr
    (fun raw ih cur =>
      match t.inCodec.get cur raw with
      | none => none
      | some (curMid, aIn) =>
        match t.rewrite curMid curMid aIn with
        | none => none
        | some aOut =>
          match t.outCodec.put curMid aOut with
          | none => none
          | some (curNext, outRaw) =>
            match ih curNext with
            | none => none
            | some (curFin, outTail) => some (curFin, outRaw :: outTail))
    (fun cur => some (cur, []))
    pkts ctx

/-- Canary 4 (`[]` zero axioms): verifies `ppsCodec_putGet`, `ppsCodec_getPut`,
multi-packet `dualContext_transcodeStream_sound` preserving effective QP
(`8 + (-2) = 0 + 6` and `8 + 1 = 0 + 9`) across `PPS` rewriting, and shows
`naiveSingleContextStream` fails (`none`) on the first `P_SLICE`. -/
theorem canary4_dualContext_pps_transcode_vs_singleContext_bug :
    let initCtx : PpsCtx := ⟨false, Int.ofNat 0⟩
    let inStream : List MediaWire :=
      [.wPps false (Int.ofNat 8), .wSliceNoWeight (Int.negSucc 1),
        .wSliceNoWeight (Int.ofNat 1)]
    let outStream : List MediaWire :=
      [.wPps true (Int.ofNat 0), .wSliceWeighted (Int.ofNat 6) 0,
        .wSliceWeighted (Int.ofNat 9) 0]
    let finIn : PpsCtx := ⟨false, Int.ofNat 8⟩
    let finOut : PpsCtx := ⟨true, Int.ofNat 0⟩
    IndexedPutGet ppsCodec ∧
    IndexedGetPut ppsCodec ∧
    transcodeStream ppsRewriteTranscoder initCtx initCtx inStream =
      some (finIn, finOut, outStream) ∧
    DownstreamParses ppsCodec initCtx outStream finOut ∧
    naiveSingleContextStream ppsRewriteTranscoder initCtx inStream = none := by
  intro initCtx inStream outStream finIn finOut
  have hStep :
      DualContextRelStep ppsRewriteTranscoder (fun _ _ => True) :=
    fun _ _ _ _ _ _ _ _ => True.intro
  have hRun :
      transcodeStream ppsRewriteTranscoder initCtx initCtx inStream =
        some (finIn, finOut, outStream) :=
    rfl
  have hSound :=
    dualContext_transcodeStream_sound ppsCodec_putGet hStep inStream
      initCtx finIn initCtx finOut outStream True.intro hRun
  exact ⟨ppsCodec_putGet, ppsCodec_getPut, hRun, hSound.2.1, rfl⟩

/-! ## Canary 5: End-to-End EBSP ↔ RBSP ↔ Bits ↔ Exp-Golomb Pipeline -/

/-- Canary 5 (`[propext]` only): composes all layers on a concrete 4-byte RBSP
containing `0x00 0x00 0x01` followed by an 8-bit `ue(0) ++ se(-2) ++ [true,
false]` syntax byte (`0b1001_0110 = 0x96`), verifying EBSP escaping, `⌊3n/2⌋`
bound, strict unescaping, bit unpacking, and exact Exp-Golomb decoding. -/
theorem canary5_layered_ebsp_rbsp_bits_and_expGolomb_pipeline :
    let synBits := encodeUe 0 ++ encodeSe (Int.negSucc 1) ++ [true, false]
    let rbsp := [0, 0, 1, 0x96]
    let ebsp := [0, 0, 3, 1, 0x96]
    synBits = writeBits 8 0x96 ∧
    rbspEscape rbsp = ebsp ∧
    ebsp.length ≤ Nat.div (3 * rbsp.length) 2 ∧
    rbspUnescapeStrict ebsp = some rbsp ∧
    (match rbspUnescapeStrict ebsp with
     | some [0, 0, 1, synByte] =>
       match decodeUe (writeBits 8 synByte) with
       | some (u0, rem1) =>
         match decodeSe rem1 with
         | some (sNeg2, tailBits) =>
           u0 = 0 ∧ sNeg2 = Int.negSucc 1 ∧ tailBits = [true, false]
         | none => False
       | none => False
     | _ => False) := by
  intro synBits rbsp ebsp
  exact ⟨rfl, rfl, rbspEscape_len_le_div2 rbsp,
    rbspUnescapeStrict_escape rbsp, ⟨rfl, rfl, rfl⟩⟩

end Anneal.MediaBits

end
