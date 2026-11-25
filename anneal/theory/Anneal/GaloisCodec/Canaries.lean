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
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes
public import Anneal.MirMemComp.Memory
public import Anneal.MirMemComp.Codecs
public import Anneal.GaloisCodec.Laws
public import Anneal.GaloisCodec.Transmute

public section

/-!
# Galois Byte-Codec & Zero-Copy Transmute Canaries (`Canaries`)

Concrete positive and negative witnesses exercising every contract and law in
`Anneal.GaloisCodec`:

1. **Canary 1 (`u8StripProvCodec` & `u8StripProvAltCodec` — Full
   `GaloisLayoutCodec` + `IntoBytes` + `FromBytes` + `FromZeros` +
   `CodecNoProv`):** 1-byte provenance-stripping `UInt8` codecs matching
   `Trusted.MirSemantics`'s scalar semantics; exercises
   `galoisLayoutCodec_iff_lowerAdjoint`, non-trivial cross-codec
   `encode_unique_of_decodeEncode_encodeLeast` and
   `decode_unique_of_galoisLayoutCodec` across distinct codecs,
   `eq_of_encode_le_encode`, and `codecFromZeros_of_codecFromBytes`.
2. **Canary 2 (`Trusted.MirSemantics.{encodeVal, decodeVal}` Parity &
   Provenance Discipline):** proves `boolStripProvCodec` agrees with
   `Trusted.MirSemantics.encodeVal` / `decodeVal` on `.bool` across arbitrary
   provenance tags, contrasts strict-provenance `ptrStrict1Codec`
   (`GaloisLayoutCodec + CodecIntoBytes + CodecWithProv + ¬ CodecNoProv`), shows
   `ptrStrict1Codec → u8StripProvCodec → ptrStrict1Codec` strips provenance
   (`= none`) even though both codecs are lawful `GaloisLayoutCodec`s
   (demonstrating necessity of `CodecNoProv ca` in scalar round-trip), and
   exercises `transmute_comp_of_total_withProv_encodeLeast` on a
   provenance-preserving middle codec.
3. **Canary 3 (`zerocopy` Trait Lattice Separation — `boolStripProvCodec` &
   `nonZeroTagCodec`):** separates `FromBytes`, `FromZeros`, and `IntoBytes`
   under `GaloisLayoutCodec` (including `GaloisLayoutCodec nonZeroTagCodec`) and
   proves `boolStripProvCodec → u8StripProvCodec` totality
   (`transmuteTotal_iff_valid_subset_of_galois`) and round-trip recovery
   (`transmute_roundtrip_of_total_intoBytes_encodeLeast_decodeEncode_noProv`).
4. **Canary 4 (Padded `#[repr(C)]` Product, Padding Characterization, &
   `CodecIntoBytes` Necessity in Composition):** exercises `pairPaddedCodec`
   at `padLen = 0` (`CodecIntoBytes`) and `padLen = 1` (`¬ CodecIntoBytes`),
   `codecNoProv_pairPadded`, both directions of `DecodeIgnoresAt`
   (`padding_uninit_of_decodeIgnores` & `decodeIgnores_of_encode_uninit`), and
   middle-padding composition failure when `CodecIntoBytes` is omitted from
   `transmute_comp_of_total_intoBytes_encodeLeast_noProv`.
5. **Canary 5 (`MemoryState` Zero-Copy Write/Read Transmute, Exact Framing, &
   Single-Cause Faults):** exercises
   `execReadDecode_after_execWriteEncode_eq_transmute` (including
   `alignWrite = 1`, `alignRead = 0` `Unaligned` read on a mixed scalar +
   provenance pair), verifies exact byte equality on allocation `0` and
   surrounding slices `[0..2)` and `[4..8)` of allocation `1`, and verifies 4
   single-cause fault regressions.
6. **Canary 6 (Single-Law Counterexamples):** `boolNonZeroBadCodec` (satisfies
   `CodecEncodeLen`, `CodecDecodeLen`, `CodecDecodeMono`, `CodecDecodeEncode`;
   violates `CodecEncodeLeast`), `exactUninitBadCodec` and
   `u8RejectProvBadCodec` (satisfy `CodecEncodeLen`, `CodecDecodeLen`,
   `CodecDecodeEncode`, `CodecEncodeLeast`; violate `CodecDecodeMono` on
   `.uninit ≤ .init` and `none ≤ some` respectively), plus
   `allocBytesLeBool_iff` reflection.
-/

namespace Anneal.GaloisCodec

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirMemComp

/-! ## Canary 1: Full `GaloisLayoutCodec` + `IntoBytes` + `FromBytes` -/

/-- Provenance-stripping 1-byte `UInt8` codec (`encode` emits `prov = none`,
`decode` accepts any provenance tag, matching `Trusted.MirSemantics`'s scalar
byte decoding). -/
@[expose] def u8StripProvCodec : ByteCodec UInt8 where
  byteSize := 1
  encode b := [.init b none]
  decode
    | [.init b _] => some b
    | _ => none

/-- Syntactically distinct 1-byte provenance-stripping `UInt8` codec using an
explicit length guard and `List.replicate`, used to exercise cross-codec
uniqueness theorems non-trivially. -/
@[expose] def u8StripProvAltCodec : ByteCodec UInt8 where
  byteSize := 1
  encode b := List.replicate 1 (.init b none)
  decode bs :=
    if Nat.beq bs.length 1 then
      match bs with
      | .init b _ :: _ => some b
      | _ => none
    else
      none

/-- `u8StripProvCodec` satisfies `GaloisLayoutCodec` under the 3-level
`OptProvLe` order. -/
theorem canary1_galois_u8StripProv : GaloisLayoutCodec u8StripProvCodec := by
  refine ⟨fun _ => rfl, ?_, ?_, fun _ => rfl, ?_⟩
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init _ _ =>
        cases rest with
        | nil => rfl
        | cons _ _ => nomatch hDec
  · intro xs ys hLe
    cases xs with
    | nil => exact True.intro
    | cons x₀ xrest =>
      cases x₀ with
      | uninit => exact True.intro
      | init bx _ =>
        cases xrest with
        | nil =>
          cases ys with
          | nil => exact False.elim hLe
          | cons y₀ yrest =>
            cases y₀ with
            | uninit => exact False.elim hLe.1
            | init by_ _ =>
              cases yrest with
              | nil => exact hLe.1.1
              | cons _ _ => exact False.elim hLe.2
        | cons _ _ => exact True.intro
  · intro bs v hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init b _ =>
        cases rest with
        | nil =>
          injection hDec with hv
          rw [← hv]
          exact ⟨⟨rfl, True.intro⟩, True.intro⟩
        | cons _ _ => nomatch hDec

/-- `u8StripProvAltCodec` agrees pointwise with `u8StripProvCodec.decode`. -/
private theorem u8StripProvAlt_decode_eq (bs : List AllocByte) :
    u8StripProvCodec.decode bs = u8StripProvAltCodec.decode bs := by
  cases bs with
  | nil => rfl
  | cons b₀ rest =>
    cases rest with
    | nil =>
      cases b₀ with
      | uninit => rfl
      | init _ _ => rfl
    | cons _ _ => cases b₀ <;> rfl

/-- `u8StripProvAltCodec` satisfies `GaloisLayoutCodec`. -/
theorem canary1_galois_u8StripProvAlt :
    GaloisLayoutCodec u8StripProvAltCodec := by
  refine ⟨fun _ => rfl, ?_, ?_, fun _ => rfl, ?_⟩
  · intro bs v hDec
    rw [← u8StripProvAlt_decode_eq bs] at hDec
    exact canary1_galois_u8StripProv.decodeLen bs v hDec
  · intro xs ys hLe
    rw [← u8StripProvAlt_decode_eq xs, ← u8StripProvAlt_decode_eq ys]
    exact canary1_galois_u8StripProv.decodeMono xs ys hLe
  · intro bs v hDec
    rw [← u8StripProvAlt_decode_eq bs] at hDec
    exact canary1_galois_u8StripProv.encodeLeast bs v hDec

/-- `u8StripProvCodec` satisfies `CodecIntoBytes`. -/
theorem canary1_intoBytes_u8StripProv : CodecIntoBytes u8StripProvCodec :=
  ⟨canary1_galois_u8StripProv.encodeLen, fun _ => rfl⟩

/-- `u8StripProvCodec` satisfies `CodecFromBytes`. -/
theorem canary1_fromBytes_u8StripProv : CodecFromBytes u8StripProvCodec := by
  intro bs hLen hInit
  cases bs with
  | nil => nomatch hLen
  | cons b₀ rest =>
    cases rest with
    | cons _ _ => nomatch hLen
    | nil =>
      cases b₀ with
      | uninit => exact Bool.noConfusion hInit
      | init b _ => exact ⟨b, rfl⟩

/-- `u8StripProvCodec` satisfies `CodecNoProv`. -/
theorem canary1_noProv_u8StripProv : CodecNoProv u8StripProvCodec :=
  fun _ => rfl

/-- `u8StripProvCodec` inherits `CodecFromZeros`, lower-adjoint equivalence,
non-trivial cross-codec encoder/decoder uniqueness against
`u8StripProvAltCodec`, and encoding injectivity. -/
theorem canary1_derived_laws :
    CodecFromZeros u8StripProvCodec ∧
    LowerAdjointCodec u8StripProvCodec ∧
    (∀ b, u8StripProvCodec.encode b = u8StripProvAltCodec.encode b) ∧
    (∀ bs, u8StripProvCodec.decode bs = u8StripProvAltCodec.decode bs) ∧
    (∀ {b₁ b₂},
      AllocBytesLe (u8StripProvCodec.encode b₁)
        (u8StripProvCodec.encode b₂) → b₁ = b₂) :=
  ⟨codecFromZeros_of_codecFromBytes canary1_fromBytes_u8StripProv,
   (galoisLayoutCodec_iff_lowerAdjoint u8StripProvCodec).mp
     canary1_galois_u8StripProv,
   encode_unique_of_decodeEncode_encodeLeast
     u8StripProvCodec u8StripProvAltCodec u8StripProvAlt_decode_eq
     canary1_galois_u8StripProv.decodeEncode
     canary1_galois_u8StripProv.encodeLeast
     canary1_galois_u8StripProvAlt.decodeEncode
     canary1_galois_u8StripProvAlt.encodeLeast,
   decode_unique_of_galoisLayoutCodec
     u8StripProvCodec u8StripProvAltCodec (fun _ => rfl)
     canary1_galois_u8StripProv
     canary1_galois_u8StripProvAlt,
   fun hLe =>
     eq_of_encode_le_encode u8StripProvCodec
       canary1_galois_u8StripProv.decodeMono
       canary1_galois_u8StripProv.decodeEncode hLe⟩

/-! ## Canary 2: `Trusted.MirSemantics` Parity & Provenance Discipline -/

/-- Rust-style 1-byte `Bool` codec (`0x00 => false`, `0x01 => true`, stripping
provenance on decode and emitting `prov = none`, matching
`Trusted.MirSemantics.{encodeVal, decodeVal}`). -/
@[expose] def boolStripProvCodec : ByteCodec Bool where
  byteSize := 1
  encode
    | false => [.init 0 none]
    | true => [.init 1 none]
  decode
    | [.init b _] =>
      if Nat.beq b.toNat 0 then
        some false
      else if Nat.beq b.toNat 1 then
        some true
      else
        none
    | _ => none

private theorem uint8Eq_zero_of_beq {b : UInt8}
    (h : Nat.beq b.toNat 0 = true) : b = 0 := by
  cases b with
  | ofBitVec bv =>
    cases bv with
    | ofFin f =>
      cases f with
      | mk v _ =>
        cases v with
        | zero => rfl
        | succ _ => exact Bool.noConfusion h

private theorem uint8Eq_one_of_beq {b : UInt8}
    (h : Nat.beq b.toNat 1 = true) : b = 1 := by
  cases b with
  | ofBitVec bv =>
    cases bv with
    | ofFin f =>
      cases f with
      | mk v _ =>
        cases v with
        | zero => exact Bool.noConfusion h
        | succ n =>
          cases n with
          | zero => rfl
          | succ _ => exact Bool.noConfusion h

private theorem uint8Eq_two_of_beq {b : UInt8}
    (h : Nat.beq b.toNat 2 = true) : b = 2 := by
  cases b with
  | ofBitVec bv =>
    cases bv with
    | ofFin f =>
      cases f with
      | mk v _ =>
        cases v with
        | zero => exact Bool.noConfusion h
        | succ n =>
          cases n with
          | zero => exact Bool.noConfusion h
          | succ m =>
            cases m with
            | zero => rfl
            | succ _ => exact Bool.noConfusion h

/-- `boolStripProvCodec` satisfies `GaloisLayoutCodec`. -/
theorem canary2_galois_boolStripProv :
    GaloisLayoutCodec boolStripProvCodec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    cases b <;> rfl
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init _ _ =>
        cases rest with
        | nil => rfl
        | cons _ _ => nomatch hDec
  · intro xs ys hLe
    cases xs with
    | nil => exact True.intro
    | cons x₀ xrest =>
      cases x₀ with
      | uninit => exact True.intro
      | init bx px =>
        cases xrest with
        | cons _ _ => exact True.intro
        | nil =>
          cases ys with
          | nil => exact False.elim hLe
          | cons y₀ yrest =>
            cases y₀ with
            | uninit => exact False.elim hLe.1
            | init by_ py =>
              cases yrest with
              | cons _ _ => exact False.elim hLe.2
              | nil =>
                have hByteEq : bx = by_ := hLe.1.1
                rw [← hByteEq]
                exact optValLe_refl
                  (boolStripProvCodec.decode [.init bx px])
  · intro b
    cases b <;> rfl
  · intro bs v hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init b _ =>
        cases rest with
        | cons _ _ => nomatch hDec
        | nil =>
          dsimp only [boolStripProvCodec] at hDec
          cases h0 : Nat.beq b.toNat 0 with
          | true =>
            rw [h0] at hDec
            injection hDec with hv
            rw [← hv, uint8Eq_zero_of_beq h0]
            exact ⟨⟨rfl, True.intro⟩, True.intro⟩
          | false =>
            rw [h0] at hDec
            cases h1 : Nat.beq b.toNat 1 with
            | true =>
              rw [h1] at hDec
              injection hDec with hv
              rw [← hv, uint8Eq_one_of_beq h1]
              exact ⟨⟨rfl, True.intro⟩, True.intro⟩
            | false =>
              rw [h1] at hDec
              nomatch hDec

/-- Direct parity against `Trusted.MirSemantics.{encodeVal, decodeVal}`
(`[propext]` only): `boolStripProvCodec` matches `Trusted.MirSemantics` on
every `Bool` encoding, on decoding valid bytes carrying arbitrary provenance
`p : Option AllocId`, on `.uninit` (`.ok none`), and on invalid byte `0x02`
(`.error .undefined`). -/
theorem canary2_boolStripProv_matches_mirSemantics :
    (∀ b : Bool,
      encodeVal .little .bool (.bool b) = .ok (boolStripProvCodec.encode b)) ∧
    (∀ (b : Bool) (p : Option AllocId),
      decodeVal .little .bool [.init (if b then 1 else 0) p] =
        .ok (some (.bool b)) ∧
      boolStripProvCodec.decode [.init (if b then 1 else 0) p] = some b) ∧
    (decodeVal .little .bool [.uninit] = .ok none ∧
      boolStripProvCodec.decode [.uninit] = none) ∧
    (∀ p : Option AllocId,
      decodeVal .little .bool [.init 2 p] = .error .undefined ∧
      boolStripProvCodec.decode [.init 2 p] = none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    rw [← execEncodeVal_eq .little .bool (.bool b)]
    cases b <;> rfl
  · intro b p
    rw [← execDecodeVal_eq .little .bool [.init (if b then 1 else 0) p]]
    cases b <;> exact ⟨rfl, rfl⟩
  · rw [← execDecodeVal_eq .little .bool [.uninit]]
    exact ⟨rfl, rfl⟩
  · intro p
    rw [← execDecodeVal_eq .little .bool [.init 2 p]]
    exact ⟨rfl, rfl⟩

/-- Strict-provenance 1-byte pointer-fragment codec requiring `some allocId`. -/
@[expose] def ptrStrict1Codec : ByteCodec (UInt8 × AllocId) where
  byteSize := 1
  encode p := [.init p.1 (some p.2)]
  decode
    | [.init b (some id)] => some (b, id)
    | _ => none

/-- Strict-provenance 1-byte swapped `(AllocId × UInt8)` codec preserving
provenance, used to exercise `transmute_comp_of_total_withProv_encodeLeast`. -/
@[expose] def ptrStrict1SwapCodec : ByteCodec (AllocId × UInt8) where
  byteSize := 1
  encode p := [.init p.2 (some p.1)]
  decode
    | [.init b (some id)] => some (id, b)
    | _ => none

/-- `ptrStrict1Codec` satisfies `GaloisLayoutCodec`. -/
theorem canary2_galois_ptrStrict1 : GaloisLayoutCodec ptrStrict1Codec := by
  refine ⟨fun _ => rfl, ?_, ?_, fun p => by cases p; rfl, ?_⟩
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init _ p =>
        cases p with
        | none => nomatch hDec
        | some _ =>
          cases rest with
          | nil => rfl
          | cons _ _ => nomatch hDec
  · intro xs ys hLe
    cases xs with
    | nil => exact True.intro
    | cons x₀ xrest =>
      cases x₀ with
      | uninit => exact True.intro
      | init bx px =>
        cases px with
        | none => exact True.intro
        | some idx =>
          cases xrest with
          | cons _ _ => exact True.intro
          | nil =>
            cases ys with
            | nil => exact False.elim hLe
            | cons y₀ yrest =>
              cases y₀ with
              | uninit => exact False.elim hLe.1
              | init by_ py =>
                cases py with
                | none => exact False.elim hLe.1.2
                | some idy =>
                  cases yrest with
                  | cons _ _ => exact False.elim hLe.2
                  | nil =>
                    dsimp only [ptrStrict1Codec, OptValLe]
                    rw [hLe.1.1, hLe.1.2]
  · intro bs v hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init b p =>
        cases p with
        | none => nomatch hDec
        | some id =>
          cases rest with
          | cons _ _ => nomatch hDec
          | nil =>
            injection hDec with hv
            rw [← hv]
            exact ⟨⟨rfl, rfl⟩, True.intro⟩

/-- `ptrStrict1SwapCodec` satisfies `CodecEncodeLeast` and `CodecWithProv`. -/
private theorem ptrStrict1Swap_encodeLeast :
    CodecEncodeLeast ptrStrict1SwapCodec := by
  intro bs v hDec
  cases bs with
  | nil => nomatch hDec
  | cons b₀ rest =>
    cases b₀ with
    | uninit => nomatch hDec
    | init b p =>
      cases p with
      | none => nomatch hDec
      | some id =>
        cases rest with
        | cons _ _ => nomatch hDec
        | nil =>
          injection hDec with hv
          rw [← hv]
          exact ⟨⟨rfl, rfl⟩, True.intro⟩

/-- Provenance-stripping round-trip counterexample and provenance-preserving
composition contrast:
1. Both `ptrStrict1Codec` and `u8StripProvCodec` satisfy `GaloisLayoutCodec`
   and `CodecIntoBytes`, and `ptrStrict1Codec → u8StripProvCodec` is total, yet
   `ptrStrict1Codec → u8StripProvCodec → ptrStrict1Codec` on `(7, 1)` returns
   `none` precisely because `¬ CodecNoProv ptrStrict1Codec`.
2. Transmuting `ptrStrict1Codec → ptrStrict1SwapCodec → u8StripProvCodec`
   composes identically via `transmute_comp_of_total_withProv_encodeLeast`
   because `CodecWithProv ptrStrict1SwapCodec` preserves provenance. -/
theorem canary2_ptr_provenance_laws :
    CodecIntoBytes ptrStrict1Codec ∧
    CodecWithProv ptrStrict1Codec ∧
    ¬ CodecNoProv ptrStrict1Codec ∧
    ¬ CodecFromZeros ptrStrict1Codec ∧
    ¬ CodecFromBytes ptrStrict1Codec ∧
    CodecTransmuteTotal ptrStrict1Codec u8StripProvCodec ∧
    Option.bind
      (codecTransmute ptrStrict1Codec u8StripProvCodec (7, 1))
      (codecTransmute u8StripProvCodec ptrStrict1Codec) = none ∧
    (∀ p : UInt8 × AllocId,
      Option.bind
        (codecTransmute ptrStrict1Codec ptrStrict1SwapCodec p)
        (codecTransmute ptrStrict1SwapCodec u8StripProvCodec) =
        codecTransmute ptrStrict1Codec u8StripProvCodec p) := by
  have hIBPtr : CodecIntoBytes ptrStrict1Codec :=
    ⟨canary2_galois_ptrStrict1.encodeLen, fun _ => rfl⟩
  have hNotNP : ¬ CodecNoProv ptrStrict1Codec := by
    intro hNP
    exact Bool.noConfusion (hNP (0, 1))
  have hNotFZ : ¬ CodecFromZeros ptrStrict1Codec := by
    intro hFZ
    cases hFZ with
    | intro _ hv => nomatch hv
  have hTotPtrToU8 : CodecTransmuteTotal ptrStrict1Codec u8StripProvCodec :=
    transmute_total_of_intoBytes_fromBytes rfl hIBPtr
      canary1_fromBytes_u8StripProv
  have hTotSwap : CodecTransmuteTotal ptrStrict1Codec ptrStrict1SwapCodec :=
    fun p => ⟨(p.2, p.1), rfl⟩
  refine ⟨hIBPtr, fun _ => rfl, hNotNP, hNotFZ,
    fun hFB => hNotFZ (codecFromZeros_of_codecFromBytes hFB),
    hTotPtrToU8, rfl, fun p =>
      transmute_comp_of_total_withProv_encodeLeast u8StripProvCodec
        hTotSwap (fun _ => rfl) ptrStrict1Swap_encodeLeast p⟩

/-! ## Canary 3: `zerocopy` Trait Separation (`Bool` & `NonZeroTag`) -/

/-- `boolStripProvCodec` satisfies `CodecIntoBytes`, `CodecFromZeros`, and
`CodecNoProv`, refutes `CodecFromBytes` on `0x02`, and transmutes totally +
invertibly through `u8StripProvCodec`. -/
theorem canary3_boolStripProv_transmute_and_traits :
    CodecIntoBytes boolStripProvCodec ∧
    CodecFromZeros boolStripProvCodec ∧
    CodecNoProv boolStripProvCodec ∧
    ¬ CodecFromBytes boolStripProvCodec ∧
    CodecTransmuteTotal boolStripProvCodec u8StripProvCodec ∧
    (∀ b : Bool,
      Option.bind
        (codecTransmute boolStripProvCodec u8StripProvCodec b)
        (codecTransmute u8StripProvCodec boolStripProvCodec) = some b) := by
  have hIB_bool : CodecIntoBytes boolStripProvCodec :=
    ⟨canary2_galois_boolStripProv.encodeLen, fun b => by cases b <;> rfl⟩
  have hNP_bool : CodecNoProv boolStripProvCodec :=
    fun b => by cases b <;> rfl
  have hTot : CodecTransmuteTotal boolStripProvCodec u8StripProvCodec := by
    apply (transmuteTotal_iff_valid_subset_of_galois
      canary2_galois_boolStripProv.decodeEncode
      canary2_galois_boolStripProv.encodeLeast
      canary1_galois_u8StripProv.decodeMono).mpr
    intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init b _ =>
        cases rest with
        | cons _ _ => nomatch hDec
        | nil => exact ⟨b, rfl⟩
  refine ⟨hIB_bool, ⟨false, rfl⟩, hNP_bool, ?_, hTot, fun b =>
    transmute_roundtrip_of_total_intoBytes_encodeLeast_decodeEncode_noProv
      hNP_bool hTot canary1_intoBytes_u8StripProv
      canary1_galois_u8StripProv.encodeLeast
      canary2_galois_boolStripProv.decodeEncode b⟩
  intro hFB
  cases hFB [.init 2 none] rfl rfl with
  | intro _ hv => nomatch hv

/-- Two-tag non-zero byte Niche type (`0x01` or `0x02`), separating
`CodecIntoBytes` from `CodecFromZeros`. -/
inductive NonZeroTag where
  | one
  | two

/-- Provenance-stripping 1-byte codec for `NonZeroTag` (`0x00` niche
invalid). -/
@[expose] def nonZeroTagCodec : ByteCodec NonZeroTag where
  byteSize := 1
  encode
    | .one => [.init 1 none]
    | .two => [.init 2 none]
  decode
    | [.init b _] =>
      if Nat.beq b.toNat 1 then
        some .one
      else if Nat.beq b.toNat 2 then
        some .two
      else
        none
    | _ => none

/-- `nonZeroTagCodec` satisfies `GaloisLayoutCodec`. -/
theorem canary3_galois_nonZeroTag : GaloisLayoutCodec nonZeroTagCodec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    cases t <;> rfl
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init _ _ =>
        cases rest with
        | nil => rfl
        | cons _ _ => nomatch hDec
  · intro xs ys hLe
    cases xs with
    | nil => exact True.intro
    | cons x₀ xrest =>
      cases x₀ with
      | uninit => exact True.intro
      | init bx px =>
        cases xrest with
        | cons _ _ => exact True.intro
        | nil =>
          cases ys with
          | nil => exact False.elim hLe
          | cons y₀ yrest =>
            cases y₀ with
            | uninit => exact False.elim hLe.1
            | init by_ _ =>
              cases yrest with
              | cons _ _ => exact False.elim hLe.2
              | nil =>
                have hByteEq : bx = by_ := hLe.1.1
                rw [← hByteEq]
                exact optValLe_refl
                  (nonZeroTagCodec.decode [.init bx px])
  · intro t
    cases t <;> rfl
  · intro bs v hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init b _ =>
        cases rest with
        | cons _ _ => nomatch hDec
        | nil =>
          dsimp only [nonZeroTagCodec] at hDec
          cases h1 : Nat.beq b.toNat 1 with
          | true =>
            rw [h1] at hDec
            injection hDec with hv
            rw [← hv, uint8Eq_one_of_beq h1]
            exact ⟨⟨rfl, True.intro⟩, True.intro⟩
          | false =>
            rw [h1] at hDec
            cases h2 : Nat.beq b.toNat 2 with
            | true =>
              rw [h2] at hDec
              injection hDec with hv
              rw [← hv, uint8Eq_two_of_beq h2]
              exact ⟨⟨rfl, True.intro⟩, True.intro⟩
            | false =>
              rw [h2] at hDec
              nomatch hDec

/-- `nonZeroTagCodec` satisfies `GaloisLayoutCodec`, `CodecIntoBytes`, and
`CodecNoProv`, while refuting `CodecFromZeros` (and hence `CodecFromBytes`). -/
theorem canary3_nonZeroTag_refutes_fromZeros :
    GaloisLayoutCodec nonZeroTagCodec ∧
    CodecIntoBytes nonZeroTagCodec ∧
    CodecNoProv nonZeroTagCodec ∧
    ¬ CodecFromZeros nonZeroTagCodec ∧
    ¬ CodecFromBytes nonZeroTagCodec := by
  have hNotFZ : ¬ CodecFromZeros nonZeroTagCodec := by
    intro hFZ
    cases hFZ with
    | intro _ ht => nomatch ht
  exact ⟨canary3_galois_nonZeroTag,
    ⟨fun t => by cases t <;> rfl, fun t => by cases t <;> rfl⟩,
    fun t => by cases t <;> rfl,
    hNotFZ, fun hFB => hNotFZ (codecFromZeros_of_codecFromBytes hFB)⟩

/-! ## Canary 4: Padded Product, Padding Laws, & Composition Tightness -/

/-- Unpadded 2-byte `UInt8 × UInt8` pair codec (`padLen = 0`). -/
@[expose] def unpaddedPair2Codec : ByteCodec (UInt8 × UInt8) :=
  pairPaddedCodec u8StripProvCodec 0 u8StripProvCodec

/-- Padded 3-byte `#[repr(C)]` pair codec with 1 middle `.uninit` padding byte
at index `1`. -/
@[expose] def paddedPair3Codec : ByteCodec (UInt8 × UInt8) :=
  pairPaddedCodec u8StripProvCodec 1 u8StripProvCodec

/-- 3-byte unpadded source codec (`CodecIntoBytes`, `CodecNoProv`) for testing
middle-padding loss across `A → B → C`. -/
@[expose] def tripleInitU8Codec : ByteCodec (UInt8 × UInt8 × UInt8) where
  byteSize := 3
  encode t := [.init t.1 none, .init t.2.1 none, .init t.2.2 none]
  decode
    | [.init a _, .init b _, .init c _] => some (a, b, c)
    | _ => none

/-- 3-byte target codec requiring all 3 bytes to be initialized. -/
@[expose] def allInit3UnitCodec : ByteCodec Unit where
  byteSize := 3
  encode _ := [.init 0 none, .init 0 none, .init 0 none]
  decode bs :=
    if Nat.beq bs.length 3 && allBytesInit bs then some () else none

/-- Exercises `galoisLayoutCodec_pairPadded`, `codecFromBytes_pairPadded`,
`codecNoProv_pairPadded`, `codecIntoBytes_pairPadded_zero`,
`not_codecIntoBytes_pairPadded_succ`, `transmute_total_of_intoBytes_fromBytes`,
both padding characterization laws (`decodeIgnores_of_encode_uninit` &
`padding_uninit_of_decodeIgnores`), and middle-padding failure when
`CodecIntoBytes` is omitted from
`transmute_comp_of_total_intoBytes_encodeLeast_noProv`. -/
theorem canary4_paddedPair_and_comp_tightness :
    GaloisLayoutCodec unpaddedPair2Codec ∧
    CodecIntoBytes unpaddedPair2Codec ∧
    CodecNoProv unpaddedPair2Codec ∧
    GaloisLayoutCodec paddedPair3Codec ∧
    CodecFromBytes paddedPair3Codec ∧
    CodecNoProv paddedPair3Codec ∧
    ¬ CodecIntoBytes paddedPair3Codec ∧
    DecodeIgnoresAt paddedPair3Codec 1 ∧
    (∀ p, listGetByte? (paddedPair3Codec.encode p) 1 = some .uninit) ∧
    CodecTransmuteTotal tripleInitU8Codec paddedPair3Codec ∧
    Option.bind
      (codecTransmute tripleInitU8Codec paddedPair3Codec (5, 9, 6))
      (codecTransmute paddedPair3Codec allInit3UnitCodec) = none ∧
    codecTransmute tripleInitU8Codec allInit3UnitCodec (5, 9, 6) = some () := by
  have hG0 := galoisLayoutCodec_pairPadded 0
    canary1_galois_u8StripProv canary1_galois_u8StripProv
  have hG1 := galoisLayoutCodec_pairPadded 1
    canary1_galois_u8StripProv canary1_galois_u8StripProv
  have hFB1 := codecFromBytes_pairPadded 1
    canary1_fromBytes_u8StripProv canary1_fromBytes_u8StripProv
  have hIB0 := codecIntoBytes_pairPadded_zero
    canary1_intoBytes_u8StripProv canary1_intoBytes_u8StripProv
  have hNP0 := codecNoProv_pairPadded 0
    canary1_noProv_u8StripProv canary1_noProv_u8StripProv
  have hNP1 := codecNoProv_pairPadded 1
    canary1_noProv_u8StripProv canary1_noProv_u8StripProv
  have hIgn1 : DecodeIgnoresAt paddedPair3Codec 1 :=
    decodeIgnores_of_encode_uninit paddedPair3Codec hG1 (fun _ => rfl)
  have hIdxLt : 1 < paddedPair3Codec.byteSize :=
    Nat.succ_lt_succ (Nat.zero_lt_succ 1)
  have hUninit1 :
      ∀ p, listGetByte? (paddedPair3Codec.encode p) 1 = some .uninit :=
    padding_uninit_of_decodeIgnores paddedPair3Codec
      hG1.encodeLen hG1.decodeEncode hG1.encodeLeast hIdxLt hIgn1
  have hIBTriple : CodecIntoBytes tripleInitU8Codec :=
    ⟨fun _ => rfl, fun _ => rfl⟩
  have hTot : CodecTransmuteTotal tripleInitU8Codec paddedPair3Codec :=
    transmute_total_of_intoBytes_fromBytes rfl hIBTriple hFB1
  exact ⟨hG0, hIB0, hNP0, hG1, hFB1, hNP1,
    not_codecIntoBytes_pairPadded_succ u8StripProvCodec 0 u8StripProvCodec
      (0, 0),
    hIgn1, hUninit1, hTot, rfl, rfl⟩

/-! ## Canary 5: `MemoryState` Zero-Copy Write/Read & Fault Regressions -/

/-- Mixed 2-byte pair codec combining a scalar `UInt8` byte and a
strict-provenance `(UInt8 × AllocId)` byte (`padLen = 0`). -/
@[expose] def mixedPair2Codec : ByteCodec (UInt8 × (UInt8 × AllocId)) :=
  pairPaddedCodec u8StripProvCodec 0 ptrStrict1Codec

/-- Swapped-order 2-byte view codec reading `[.init b₀ _, .init b₁ (some id)]`
as `((b₁, id), b₀)`. -/
@[expose] def swappedMixedPair2Codec :
    ByteCodec ((UInt8 × AllocId) × UInt8) where
  byteSize := 2
  encode p := [.init p.2 none, .init p.1.1 (some p.1.2)]
  decode
    | [.init b₀ _, .init b₁ (some id)] => some ((b₁, id), b₀)
    | _ => none

/-- Base `MemoryState` containing an immutable allocation `0` (`4` bytes) prior
to appending the target allocation `1`. -/
@[expose] def canary5BaseMem : MemoryState :=
  { nextAllocId := 2
    allocations :=
      [{ allocId := 0
         alignLog2 := 0
         mutability := .shared
         bytes := List.replicate 4 (.init 0xFF none)
         live := true }] }

/-- Fresh 8-byte mutable allocation `1` (`alignLog2 = 2`, 4-byte aligned). -/
@[expose] def canary5TargetAlloc : Allocation :=
  { allocId := 1
    alignLog2 := 2
    mutability := .mut
    bytes := List.replicate 8 .uninit
    live := true }

/-- End-to-end `MemoryState` zero-copy transmute witness:
1. Instantiates `execReadDecode_after_execWriteEncode_eq_transmute` writing
   `mixedPair2Codec` at offset `2` (`alignWrite = 1`, 2-byte aligned) and
   reading `swappedMixedPair2Codec` at `alignRead = 0` (`zerocopy::Unaligned`
   1-byte-aligned read), yielding `.ok (some ((0x55, 0), 0xAA))`.
2. Verifies exact byte-slice equality on surrounding allocation `0` (`[0..4)`)
   and surrounding bytes `[0..2)` and `[4..8)` of allocation `1`.
3. Verifies 4 single-cause fault regressions (`live = false`, `.shared`
   mutability, out-of-bounds offset `7`, and over-aligned `alignWrite = 2` at
   offset `2`). -/
theorem canary5_memoryState_transmute_and_faults :
    let m₀ : MemoryState :=
      { canary5BaseMem with
        allocations := canary5BaseMem.allocations ++ [canary5TargetAlloc] }
    let val : UInt8 × (UInt8 × AllocId) := (0xAA, (0x55, 0))
    (match execWriteEncode mixedPair2Codec m₀ ⟨1, 2⟩ 1 val with
     | .error fk => Except.error fk
     | .ok m₁ => execReadDecode swappedMixedPair2Codec m₁ ⟨1, 2⟩ 0) =
      Except.ok (some ((0x55, 0), 0xAA)) ∧
    (match execWriteEncode mixedPair2Codec m₀ ⟨1, 2⟩ 1 val with
     | .error fk => Except.error fk
     | .ok m₁ => execReadBytes m₁ ⟨0, 0⟩ 4 0) =
      Except.ok (List.replicate 4 (.init 0xFF none)) ∧
    (match execWriteEncode mixedPair2Codec m₀ ⟨1, 2⟩ 1 val with
     | .error fk => Except.error fk
     | .ok m₁ => execReadBytes m₁ ⟨1, 0⟩ 2 0) =
      Except.ok [.uninit, .uninit] ∧
    (match execWriteEncode mixedPair2Codec m₀ ⟨1, 2⟩ 1 val with
     | .error fk => Except.error fk
     | .ok m₁ => execReadBytes m₁ ⟨1, 4⟩ 4 0) =
      Except.ok (List.replicate 4 .uninit) ∧
    execWriteEncode mixedPair2Codec
      { canary5BaseMem with
        allocations :=
          canary5BaseMem.allocations ++
            [{ canary5TargetAlloc with live := false }] }
      ⟨1, 2⟩ 1 val = .error .undefined ∧
    execWriteEncode mixedPair2Codec
      { canary5BaseMem with
        allocations :=
          canary5BaseMem.allocations ++
            [{ canary5TargetAlloc with mutability := .shared }] }
      ⟨1, 2⟩ 1 val = .error .undefined ∧
    execWriteEncode mixedPair2Codec m₀ ⟨1, 7⟩ 0 val = .error .undefined ∧
    execWriteEncode mixedPair2Codec m₀ ⟨1, 2⟩ 2 val = .error .undefined := by
  intro m₀ val
  have hBridge :=
    execReadDecode_after_execWriteEncode_eq_transmute
      mixedPair2Codec swappedMixedPair2Codec canary5BaseMem canary5TargetAlloc
      2 1 0 val rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact ⟨hBridge, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Canary 6: Single-Cause Representation Law Regressions -/

/-- Non-canonical C-style `Bool` codec (`0 => false`, any non-zero => `true`,
stripping provenance): satisfies `CodecEncodeLen`, `CodecDecodeLen`,
`CodecDecodeMono`, and `CodecDecodeEncode`, while violating `CodecEncodeLeast`
on `[.init 2 none]`. -/
@[expose] def boolNonZeroBadCodec : ByteCodec Bool where
  byteSize := 1
  encode
    | false => [.init 0 none]
    | true => [.init 1 none]
  decode
    | [.init b _] => some (!Nat.beq b.toNat 0)
    | _ => none

/-- Uninit-observing codec (`[.uninit] => some false`,
`[.init 1 _] => some true`, `_ => none`): satisfies `CodecEncodeLen`,
`CodecDecodeLen`, `CodecDecodeEncode`, and `CodecEncodeLeast`, while violating
`CodecDecodeMono` on `[.uninit] ≤ [.init 0 none]`. -/
@[expose] def exactUninitBadCodec : ByteCodec Bool where
  byteSize := 1
  encode
    | false => [.uninit]
    | true => [.init 1 none]
  decode
    | [.uninit] => some false
    | [.init b _] => if Nat.beq b.toNat 1 then some true else none
    | _ => none

/-- Provenance-forbidding 1-byte `UInt8` codec (`[.init b none] => some b`,
rejecting any `some id`): satisfies `CodecEncodeLen`, `CodecDecodeLen`,
`CodecDecodeEncode`, and `CodecEncodeLeast`, while violating `CodecDecodeMono`
on `[.init 7 none] ≤ [.init 7 (some 1)]`. -/
@[expose] def u8RejectProvBadCodec : ByteCodec UInt8 where
  byteSize := 1
  encode b := [.init b none]
  decode
    | [.init b none] => some b
    | _ => none

/-- Confirms independence of `CodecEncodeLeast` and `CodecDecodeMono` (both
`.uninit ≤ .init` and `none ≤ some` monotonicity) inside `GaloisLayoutCodec`,
together with `CodecEncodeLen`, `CodecDecodeLen`, and boolean reflection
`allocBytesLeBool_iff`. -/
theorem canary6_law_independence :
    CodecEncodeLen boolNonZeroBadCodec ∧
    CodecDecodeLen boolNonZeroBadCodec ∧
    CodecDecodeMono boolNonZeroBadCodec ∧
    CodecDecodeEncode boolNonZeroBadCodec ∧
    ¬ CodecEncodeLeast boolNonZeroBadCodec ∧
    CodecEncodeLen exactUninitBadCodec ∧
    CodecDecodeLen exactUninitBadCodec ∧
    CodecDecodeEncode exactUninitBadCodec ∧
    CodecEncodeLeast exactUninitBadCodec ∧
    ¬ CodecDecodeMono exactUninitBadCodec ∧
    CodecEncodeLen u8RejectProvBadCodec ∧
    CodecDecodeLen u8RejectProvBadCodec ∧
    CodecDecodeEncode u8RejectProvBadCodec ∧
    CodecEncodeLeast u8RejectProvBadCodec ∧
    ¬ CodecDecodeMono u8RejectProvBadCodec ∧
    AllocBytesLe [.uninit, .init 4 none]
      [.init 9 none, .init 4 (some 2)] := by
  refine ⟨fun b => by cases b <;> rfl, ?_, ?_, fun b => by cases b <;> rfl,
    ?_, fun b => by cases b <;> rfl, ?_, fun b => by cases b <;> rfl,
    ?_, ?_, fun _ => rfl, ?_, fun _ => rfl, ?_, ?_,
    (allocBytesLeBool_iff
      [.uninit, .init 4 none]
      [.init 9 none, .init 4 (some 2)]).mp rfl⟩
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init _ _ =>
        cases rest with
        | nil => rfl
        | cons _ _ => nomatch hDec
  · intro xs ys hLe
    cases xs with
    | nil => exact True.intro
    | cons x₀ xrest =>
      cases x₀ with
      | uninit => exact True.intro
      | init bx px =>
        cases xrest with
        | cons _ _ => exact True.intro
        | nil =>
          cases ys with
          | nil => exact False.elim hLe
          | cons y₀ yrest =>
            cases y₀ with
            | uninit => exact False.elim hLe.1
            | init by_ _ =>
              cases yrest with
              | cons _ _ => exact False.elim hLe.2
              | nil =>
                have hByteEq : bx = by_ := hLe.1.1
                rw [← hByteEq]
                exact optValLe_refl
                  (boolNonZeroBadCodec.decode [.init bx px])
  · intro hEL
    have hLe := hEL [.init 2 none] true rfl
    have hByteEq : (1 : UInt8) = (2 : UInt8) := hLe.1.1
    have hToNatEq : (1 : UInt8).toNat = (2 : UInt8).toNat :=
      congrArg UInt8.toNat hByteEq
    exact Nat.noConfusion (Nat.succ.inj hToNatEq)
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit =>
        cases rest with
        | nil => rfl
        | cons _ _ => nomatch hDec
      | init _ _ =>
        cases rest with
        | nil => rfl
        | cons _ _ => nomatch hDec
  · intro bs v hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit =>
        cases rest with
        | cons _ _ => nomatch hDec
        | nil =>
          injection hDec with hv
          rw [← hv]
          exact ⟨True.intro, True.intro⟩
      | init b _ =>
        cases rest with
        | cons _ _ => nomatch hDec
        | nil =>
          dsimp only [exactUninitBadCodec] at hDec
          cases h1 : Nat.beq b.toNat 1 with
          | false =>
            rw [h1] at hDec
            nomatch hDec
          | true =>
            rw [h1] at hDec
            injection hDec with hv
            rw [← hv, uint8Eq_one_of_beq h1]
            exact ⟨⟨rfl, True.intro⟩, True.intro⟩
  · intro hMono
    have h := hMono [.uninit] [.init 0 none] ⟨True.intro, True.intro⟩
    exact False.elim h
  · intro bs _ hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init _ p =>
        cases p with
        | some _ => nomatch hDec
        | none =>
          cases rest with
          | nil => rfl
          | cons _ _ => nomatch hDec
  · intro bs v hDec
    cases bs with
    | nil => nomatch hDec
    | cons b₀ rest =>
      cases b₀ with
      | uninit => nomatch hDec
      | init b p =>
        cases p with
        | some _ => nomatch hDec
        | none =>
          cases rest with
          | cons _ _ => nomatch hDec
          | nil =>
            injection hDec with hv
            rw [← hv]
            exact ⟨⟨rfl, True.intro⟩, True.intro⟩
  · intro hMono
    have h := hMono [.init 7 none] [.init 7 (some 1)]
      ⟨⟨rfl, True.intro⟩, True.intro⟩
    exact False.elim h

end Anneal.GaloisCodec

end
