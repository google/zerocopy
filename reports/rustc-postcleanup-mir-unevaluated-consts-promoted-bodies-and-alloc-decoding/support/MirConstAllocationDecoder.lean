-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Algebraic `ConstValue` / `ConstAllocation` Decoder (`MirConstAllocationDecoder.lean`)

Pinned to Lean 4.34.1 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).

This self-contained mechanization formalizes:
1. Low-level `rustc` `ConstValue`, `Allocation` (`bytes`, `initMask`, `provenance`, `align`),
   `GlobalAlloc`, and `TyLayout` (primitives, arrays, padded structs/tuples, single/direct-tag/niche
   enums, references, and slices).
2. The deterministic layout-guided algebraic decoder (`decodeConstValue` / `decodeAllocAt`) mapping
   low-level CTFE `ConstValue` and `GlobalAlloc` byte buffers into pure algebraic `PureConst` trees
   while enforcing bounds, per-byte initialization on scalar/tag leaves, and provenance isolation.
3. Mechanized soundness and invariance theorems:
   - **Theorem 1**: Padding-byte and uninitialized-gap invariance (`decodeFromAlloc_struct_padding_invariant`,
     `decodeAllocAt_struct_padding_invariant`, and concrete `(u8, u32)` padding invariance).
   - **Theorem 2**: `AllocId` renaming / address-independence invariance (`decodeConstValue_remap_invariant`).
   - **Theorem 3**: Provenance-forgery rejection (`decodeAllocAt_int_rejects_provenance`,
     `decodeAllocAt_bool_rejects_provenance`, `decodeAllocAt_enum_tag_rejects_provenance`).
   - **Theorem 4**: Uninitialized-scalar rejection (`decodeAllocAt_int_rejects_uninit`,
     `decodeAllocAt_bool_rejects_uninit`, `decodeAllocAt_niche_tag_rejects_uninit`,
     `decodeAllocAt_ref_rejects_uninit`).
   - **Theorem 5**: Canonical encoder and round-trip soundness (`encode_decode_roundtrip`) across
     symbolic and concrete golden test cases (Starnix `U64Range`, `U64ScalarValueData::UNINITIALIZED`,
     padded `(u8, u32)`, niche `Option<bool>` and `Option<NonZeroU64>`, promoted `&U64Range`, and
     `assert_eq!` promoted `(&0u32, &"assertion failed")`).
   - **Theorem 6**: Small-step promoted MIR body execution vs. eager CTFE `ConstValue` decoding
     equivalence (`promoted_body_exec_eq_ctfe_decode`).
-/

namespace MirConstAllocationDecoder

/-! ## Section 1: Low-Level `rustc` `ConstValue`, `GlobalAlloc`, and `TyLayout` -/

abbrev AllocId := Nat
abbrev DefId := Nat
abbrev FnId := Nat
abbrev AdtId := Nat
abbrev Byte := UInt8

/-- Per-byte initialization bitmask (`rustc_middle::mir::interpret::InitMask`). -/
abbrev InitMask := List Bool

/-- Pointer provenance target (`(AllocId, Offset)`). -/
structure ProvPtr where
  allocId : AllocId
  offset : Nat
  deriving BEq, DecidableEq, Repr

/-- Provenance map associating byte offsets within an allocation with pointer provenance. -/
abbrev ProvenanceMap := List (Nat × ProvPtr)

/-- Low-level CTFE byte allocation (`rustc_middle::mir::interpret::Allocation`). -/
structure Allocation where
  bytes : List Byte
  initMask : InitMask
  provenance : ProvenanceMap
  align : Nat
  deriving BEq, DecidableEq, Repr

/-- Global allocation table entry (`rustc_middle::mir::interpret::GlobalAlloc`). -/
inductive GlobalAlloc where
  | memory (alloc : Allocation)
  | staticDef (defId : DefId)
  | fnPtr (fnId : FnId)
  deriving BEq, DecidableEq, Repr

/-- Environment mapping `AllocId`s to `GlobalAlloc` entries. -/
abbrev AllocEnv := AllocId → Option GlobalAlloc

/-- Low-level CTFE scalar value (`rustc_middle::mir::interpret::Scalar`). -/
inductive ScalarVal where
  | int (val : Nat) (sizeBytes : Nat)
  | ptr (target : ProvPtr) (sizeBytes : Nat)
  deriving BEq, DecidableEq, Repr

/-- Low-level MIR `ConstValue` (`rustc_middle::mir::ConstValue`). -/
inductive ConstValue where
  | zeroSized
  | scalar (s : ScalarVal)
  | slice (allocId : AllocId) (metaLen : Nat)
  | indirect (allocId : AllocId) (offset : Nat)
  deriving BEq, DecidableEq, Repr

/-- Enum tag encoding strategies in `rustc_abi::Variants`. -/
inductive EnumTagEncoding where
  /-- Uninhabited (`none`) or single-variant (`some variantIdx`) enum with no tag bytes. -/
  | single (variantIdx : Option Nat)
  /-- Direct discriminant tag at `tagOffset` of width `tagBits` (`Variants::Multiple`, `TagEncoding::Direct`). -/
  | directTag (tagOffset : Nat) (tagBits : Nat) (tagSigned : Bool)
      (discriminants : List (Nat × Int))
  /-- Niche-encoded tag (`Variants::Multiple`, `TagEncoding::Niche`). -/
  | nicheTag (tagOffset : Nat) (tagBits : Nat) (untaggedVariant : Nat)
      (nicheVariantsStart : Nat) (nicheVariantsEnd : Nat) (nicheStart : Nat)
  deriving BEq, DecidableEq, Repr

/-- Type and ABI layout descriptor guiding constant decoding (`TyAndLayout`). -/
inductive TyLayout where
  | unit
  | bool
  | int (bits : Nat) (signed : Bool)
  | tuple (fields : List (Nat × TyLayout)) (totalSize : Nat)
  | struct (adtId : AdtId) (fields : List (Nat × TyLayout)) (totalSize : Nat)
  | array (elemTy : TyLayout) (elemStride : Nat) (count : Nat)
  | enumLayout (adtId : AdtId) (tagEncoding : EnumTagEncoding)
      (variants : List (Nat × List (Nat × TyLayout))) (totalSize : Nat)
  | ref (pointee : TyLayout)
  | sliceRef (elemTy : TyLayout) (elemStride : Nat)
  deriving Repr

/-- Byte size of a `TyLayout` on a 64-bit target (`LP64`). -/
def TyLayout.byteSize : TyLayout → Nat
  | .unit => 0
  | .bool => 1
  | .int bits _ => bits / 8
  | .tuple _ totalSize => totalSize
  | .struct _ _ totalSize => totalSize
  | .array _ elemStride count => elemStride * count
  | .enumLayout _ _ _ totalSize => totalSize
  | .ref _ => 8
  | .sliceRef _ _ => 16

/-! ## Section 2: Pure Algebraic Target (`PureConst`) and Layout-Guided Decoder -/

/-- Pure algebraic constant representation (`PureConst`), completely free of `AllocId`s,
padding bytes, and memory addresses. -/
inductive PureConst where
  | unit
  | bool (b : Bool)
  | int (bits : Nat) (signed : Bool) (val : Nat)
  | tuple (fields : List PureConst)
  | struct (adtId : AdtId) (fields : List PureConst)
  | array (elems : List PureConst)
  | enumVariant (adtId : AdtId) (variantIdx : Nat) (payload : List PureConst)
  | slice (elems : List PureConst)
  | ref (target : PureConst)
  deriving BEq, Repr

/-- Closed set of fail-closed decoding errors. -/
inductive DecodeError where
  | outOfFuel
  | missingAlloc
  | unexpectedGlobalAllocKind
  | outOfBounds
  | uninitializedBytes
  | unexpectedProvenanceInScalar
  | missingPointerProvenance
  | invalidBoolByte (byteVal : Nat)
  | uninhabitedEnum
  | invalidDiscriminant (rawTag : Nat)
  | unknownVariant (variantIdx : Nat)
  | layoutConstValueMismatch
  deriving BEq, DecidableEq, Repr

/-- Little-endian byte reader over `List Byte`. -/
def readLeBytes (bytes : List Byte) (offset : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (bytes.getD offset 0).toNat + 256 * readLeBytes bytes (offset + 1) k

/-- Read an 8-byte pointer-sized little-endian natural (used for slice metadata length). -/
def readPtrWidthNat (bytes : List Byte) (offset : Nat) : Nat :=
  readLeBytes bytes offset 8

/-- Little-endian byte writer producing `count` bytes from `val`. -/
def writeLeBytes (val : Nat) : Nat → List Byte
  | 0 => []
  | k + 1 => UInt8.ofNat (val % 256) :: writeLeBytes (val / 256) k

/-- Check whether byte at `offset` is marked initialized. -/
def checkInitByte (mask : InitMask) (offset : Nat) : Bool :=
  mask.getD offset false

/-- Check whether all bytes in `[baseOffset, baseOffset + byteWidth)` are initialized. -/
def checkInitRangeBytes (mask : InitMask) (baseOffset : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => checkInitByte mask baseOffset && checkInitRangeBytes mask (baseOffset + 1) k

/-- Bit-width wrapper for `checkInitRangeBytes`. -/
def checkInitRange (mask : InitMask) (baseOffset : Nat) (bitWidth : Nat) : Bool :=
  checkInitRangeBytes mask baseOffset (bitWidth / 8)

/-- Check whether `prov` has any provenance entry in `[baseOffset, baseOffset + byteWidth)`. -/
def hasProvenanceInRange : ProvenanceMap → Nat → Nat → Bool
  | [], _, _ => false
  | (off, _) :: rest, baseOffset, byteWidth =>
    (Nat.ble baseOffset off && Nat.blt off (baseOffset + byteWidth)) ||
      hasProvenanceInRange rest baseOffset byteWidth

/-- Check that `prov` has zero provenance entries in `[baseOffset, baseOffset + byteWidth)`. -/
def noProvenanceInRange (prov : ProvenanceMap) (baseOffset : Nat) (byteWidth : Nat) : Bool :=
  !hasProvenanceInRange prov baseOffset byteWidth

/-- Look up provenance at an exact byte offset. -/
def lookupProvenanceAt : ProvenanceMap → Nat → Option ProvPtr
  | [], _ => none
  | (off, ptr) :: rest, offset =>
    if off == offset then some ptr else lookupProvenanceAt rest offset

/-- Require an exact provenance entry at `baseOffset` and no stray provenance in the remaining
bytes `[baseOffset + 1, baseOffset + ptrByteWidth)`. -/
def lookupExactProvenance (prov : ProvenanceMap) (baseOffset : Nat) (ptrByteWidth : Nat) :
    Option ProvPtr :=
  if noProvenanceInRange prov (baseOffset + 1) (ptrByteWidth - 1) then
    lookupProvenanceAt prov baseOffset
  else
    none

/-- Convert an unsigned `bits`-bit natural into a two's-complement signed `Int`. -/
def toSignedInt (bits : Nat) (raw : Nat) : Int :=
  let half := 2 ^ (bits - 1)
  let modulus := 2 ^ bits
  if Nat.blt raw half then
    Int.ofNat raw
  else
    Int.ofNat raw - Int.ofNat modulus

/-- Look up a discriminant value in `discriminants : List (Nat × Int)`. -/
def findDiscriminantVariant : List (Nat × Int) → Int → Option Nat
  | [], _ => none
  | (vIdx, dVal) :: rest, tagVal =>
    if dVal == tagVal then some vIdx else findDiscriminantVariant rest tagVal

/-- Look up a variant's field layout list by `variantIdx`. -/
def findVariantFields : List (Nat × List (Nat × TyLayout)) → Nat → Option (List (Nat × TyLayout))
  | [], _ => none
  | (vIdx, fields) :: rest, targetIdx =>
    if vIdx == targetIdx then some fields else findVariantFields rest targetIdx

/-- Decode a 1-byte boolean leaf at `baseOffset`. -/
def decodeBoolLeaf (alloc : Allocation) (baseOffset : Nat) : Except DecodeError PureConst :=
  if !checkInitRangeBytes alloc.initMask baseOffset 1 then
    .error .uninitializedBytes
  else if !noProvenanceInRange alloc.provenance baseOffset 1 then
    .error .unexpectedProvenanceInScalar
  else
    let b := (alloc.bytes.getD baseOffset 0).toNat
    if b == 0 then
      .ok (.bool false)
    else if b == 1 then
      .ok (.bool true)
    else
      .error (.invalidBoolByte b)

/-- Decode a `(bits / 8)`-byte integer leaf at `baseOffset`. -/
def decodeIntLeaf (alloc : Allocation) (baseOffset bits : Nat) (signed : Bool) :
    Except DecodeError PureConst :=
  let byteWidth := bits / 8
  if !checkInitRangeBytes alloc.initMask baseOffset byteWidth then
    .error .uninitializedBytes
  else if !noProvenanceInRange alloc.provenance baseOffset byteWidth then
    .error .unexpectedProvenanceInScalar
  else
    .ok (.int bits signed (readLeBytes alloc.bytes baseOffset byteWidth))

/-- Validate and extract an 8-byte thin pointer at `baseOffset`. -/
def checkRefHeader (alloc : Allocation) (baseOffset : Nat) : Except DecodeError ProvPtr :=
  if !checkInitRangeBytes alloc.initMask baseOffset 8 then
    .error .uninitializedBytes
  else
    match lookupExactProvenance alloc.provenance baseOffset 8 with
    | none => .error .missingPointerProvenance
    | some ptr => .ok ptr

/-- Validate and extract a 16-byte slice fat pointer `(dataPtr, metaLen)` at `baseOffset`. -/
def checkSliceRefHeader (alloc : Allocation) (baseOffset : Nat) :
    Except DecodeError (ProvPtr × Nat) :=
  if !checkInitRangeBytes alloc.initMask baseOffset 16 then
    .error .uninitializedBytes
  else if !noProvenanceInRange alloc.provenance (baseOffset + 8) 8 then
    .error .unexpectedProvenanceInScalar
  else
    match lookupExactProvenance alloc.provenance baseOffset 8 with
    | none => .error .missingPointerProvenance
    | some ptr => .ok (ptr, readPtrWidthNat alloc.bytes (baseOffset + 8))

/-- Resolve the active `variantIdx` of an enum inside `alloc` at `baseOffset`. -/
def decodeEnumVariantIdx (alloc : Allocation) (baseOffset : Nat) :
    EnumTagEncoding → Except DecodeError Nat
  | .single optIdx =>
    match optIdx with
    | none => .error .uninhabitedEnum
    | some vIdx => .ok vIdx
  | .directTag tagOff tagBits tagSigned discrs =>
    let byteWidth := tagBits / 8
    let absOff := baseOffset + tagOff
    if !checkInitRangeBytes alloc.initMask absOff byteWidth then
      .error .uninitializedBytes
    else if !noProvenanceInRange alloc.provenance absOff byteWidth then
      .error .unexpectedProvenanceInScalar
    else
      let rawTag := readLeBytes alloc.bytes absOff byteWidth
      let tagVal := if tagSigned then toSignedInt tagBits rawTag else Int.ofNat rawTag
      match findDiscriminantVariant discrs tagVal with
      | some vIdx => .ok vIdx
      | none => .error (.invalidDiscriminant rawTag)
  | .nicheTag tagOff tagBits untaggedVar nicheStartVar nicheEndVar nicheStartVal =>
    let byteWidth := tagBits / 8
    let absOff := baseOffset + tagOff
    if !checkInitRangeBytes alloc.initMask absOff byteWidth then
      .error .uninitializedBytes
    else if !noProvenanceInRange alloc.provenance absOff byteWidth then
      .error .unexpectedProvenanceInScalar
    else
      let rawTag := readLeBytes alloc.bytes absOff byteWidth
      let modulus := 2 ^ tagBits
      let nicheCount := nicheEndVar + 1 - nicheStartVar
      let relative := (rawTag + modulus - (nicheStartVal % modulus)) % modulus
      if Nat.blt relative nicheCount then
        .ok (nicheStartVar + relative)
      else
        .ok untaggedVar

/-- Look up a memory allocation in `env`, rejecting missing or non-memory `GlobalAlloc` entries. -/
def lookupMemoryAlloc (env : AllocEnv) (allocId : AllocId) : Except DecodeError Allocation :=
  match env allocId with
  | none => .error .missingAlloc
  | some (.memory alloc) => .ok alloc
  | some (.staticDef _) => .error .unexpectedGlobalAllocKind
  | some (.fnPtr _) => .error .unexpectedGlobalAllocKind

/-- Decode a list of `(relativeOffset, fieldLayout)` pairs using a step function. -/
def decodeFieldList (step : Nat → TyLayout → Except DecodeError PureConst) (baseOffset : Nat) :
    List (Nat × TyLayout) → Except DecodeError (List PureConst)
  | [] => .ok []
  | (relOff, fLayout) :: rest => do
    let v ← step (baseOffset + relOff) fLayout
    let vs ← decodeFieldList step baseOffset rest
    .ok (v :: vs)

/-- Decode `count` homogeneous elements at stride `elemStride` starting at `baseOffset`. -/
def decodeStrideList (step : Nat → TyLayout → Except DecodeError PureConst)
    (baseOffset : Nat) (elemTy : TyLayout) (elemStride : Nat) :
    Nat → Except DecodeError (List PureConst)
  | 0 => .ok []
  | k + 1 => do
    let v ← step baseOffset elemTy
    let vs ← decodeStrideList step (baseOffset + elemStride) elemTy elemStride k
    .ok (v :: vs)

/-- Deterministic layout-guided decoder reading from an `Allocation` at `baseOffset`. -/
def decodeFromAlloc (env : AllocEnv) :
    Nat → Allocation → Nat → TyLayout → Except DecodeError PureConst
  | 0, _, _, _ => .error .outOfFuel
  | fuel + 1, alloc, baseOffset, layout =>
    if Nat.blt alloc.bytes.length (baseOffset + layout.byteSize) then
      .error .outOfBounds
    else
      match layout with
      | .unit => .ok .unit
      | .bool => decodeBoolLeaf alloc baseOffset
      | .int bits signed => decodeIntLeaf alloc baseOffset bits signed
      | .tuple fields _ => do
        let vals ← decodeFieldList (decodeFromAlloc env fuel alloc) baseOffset fields
        .ok (.tuple vals)
      | .struct adtId fields _ => do
        let vals ← decodeFieldList (decodeFromAlloc env fuel alloc) baseOffset fields
        .ok (.struct adtId vals)
      | .array elemTy elemStride count => do
        let vals ← decodeStrideList (decodeFromAlloc env fuel alloc) baseOffset elemTy elemStride count
        .ok (.array vals)
      | .enumLayout adtId tagEnc variants _ => do
        let vIdx ← decodeEnumVariantIdx alloc baseOffset tagEnc
        match findVariantFields variants vIdx with
        | none => .error (.unknownVariant vIdx)
        | some payloadFields => do
          let vals ← decodeFieldList (decodeFromAlloc env fuel alloc) baseOffset payloadFields
          .ok (.enumVariant adtId vIdx vals)
      | .ref pointee => do
        let ptr ← checkRefHeader alloc baseOffset
        let targetAlloc ← lookupMemoryAlloc env ptr.allocId
        let targetVal ← decodeFromAlloc env fuel targetAlloc ptr.offset pointee
        .ok (.ref targetVal)
      | .sliceRef elemTy elemStride => do
        let (ptr, metaLen) ← checkSliceRefHeader alloc baseOffset
        let targetAlloc ← lookupMemoryAlloc env ptr.allocId
        let elems ←
          decodeStrideList (decodeFromAlloc env fuel targetAlloc) ptr.offset elemTy elemStride metaLen
        .ok (.slice elems)

/-- Decode a `PureConst` at `(allocId, baseOffset)` in `env`. -/
def decodeAllocAt (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (baseOffset : Nat)
    (layout : TyLayout) : Except DecodeError PureConst := do
  let alloc ← lookupMemoryAlloc env allocId
  decodeFromAlloc env fuel alloc baseOffset layout

/-- Synthesize a temporary provenance-free `Allocation` holding a `sizeBytes`-byte scalar `raw`. -/
def scalarIntAllocation (raw : Nat) (sizeBytes : Nat) : Allocation :=
  { bytes := writeLeBytes raw sizeBytes
    initMask := List.replicate sizeBytes true
    provenance := []
    align := sizeBytes }

/-- Decode a top-level `rustc` `ConstValue` given its `TyLayout` and `AllocEnv`. -/
def decodeConstValue (env : AllocEnv) (fuel : Nat) (cv : ConstValue) (layout : TyLayout) :
    Except DecodeError PureConst :=
  match cv with
  | .zeroSized =>
    if layout.byteSize != 0 then
      .error .layoutConstValueMismatch
    else
      decodeFromAlloc env fuel (scalarIntAllocation 0 0) 0 layout
  | .scalar (.int raw sizeBytes) =>
    if layout.byteSize != sizeBytes then
      .error .layoutConstValueMismatch
    else
      decodeFromAlloc env fuel (scalarIntAllocation raw sizeBytes) 0 layout
  | .scalar (.ptr target sizeBytes) =>
    match layout with
    | .ref pointee =>
      if sizeBytes != 8 then
        .error .layoutConstValueMismatch
      else do
        let targetVal ← decodeAllocAt env fuel target.allocId target.offset pointee
        .ok (.ref targetVal)
    | _ => .error .layoutConstValueMismatch
  | .slice allocId metaLen =>
    match layout with
    | .sliceRef elemTy elemStride =>
      match fuel with
      | 0 => .error .outOfFuel
      | fuel' + 1 => do
        let targetAlloc ← lookupMemoryAlloc env allocId
        if Nat.blt targetAlloc.bytes.length (metaLen * elemStride) then
          .error .outOfBounds
        else do
          let elems ←
            decodeStrideList (decodeFromAlloc env fuel' targetAlloc) 0 elemTy elemStride metaLen
          .ok (.slice elems)
    | _ => .error .layoutConstValueMismatch
  | .indirect allocId offset =>
    decodeAllocAt env fuel allocId offset layout

/-! ## Section 3: Soundness & Invariance Theorems (Theorems 1–4) -/

/-- Congruence of `readLeBytes` when two byte buffers agree on `[offset, offset + count)`. -/
theorem readLeBytes_congr (b1 b2 : List Byte) (offset : Nat) :
    ∀ (count : Nat),
      (∀ i < count, b1.getD (offset + i) 0 = b2.getD (offset + i) 0) →
      readLeBytes b1 offset count = readLeBytes b2 offset count
  | 0, _ => rfl
  | k + 1, h => by
    simp only [readLeBytes]
    have h0 : b1.getD offset 0 = b2.getD offset 0 := by
      have := h 0 (Nat.zero_lt_succ k)
      simpa [Nat.add_zero] using this
    have hk : readLeBytes b1 (offset + 1) k = readLeBytes b2 (offset + 1) k := by
      apply readLeBytes_congr b1 b2 (offset + 1) k
      intro i hi
      have := h (i + 1) (Nat.succ_lt_succ hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    rw [h0, hk]

/-- Congruence of `checkInitRangeBytes` when two `InitMask`s agree on `[offset, offset + count)`. -/
theorem checkInitRangeBytes_congr (m1 m2 : InitMask) (offset : Nat) :
    ∀ (count : Nat),
      (∀ i < count, checkInitByte m1 (offset + i) = checkInitByte m2 (offset + i)) →
      checkInitRangeBytes m1 offset count = checkInitRangeBytes m2 offset count
  | 0, _ => rfl
  | k + 1, h => by
    simp only [checkInitRangeBytes]
    have h0 : checkInitByte m1 offset = checkInitByte m2 offset := by
      have := h 0 (Nat.zero_lt_succ k)
      simpa [Nat.add_zero] using this
    have hk : checkInitRangeBytes m1 (offset + 1) k = checkInitRangeBytes m2 (offset + 1) k := by
      apply checkInitRangeBytes_congr m1 m2 (offset + 1) k
      intro i hi
      have := h (i + 1) (Nat.succ_lt_succ hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    rw [h0, hk]

/-- Congruence of `decodeFieldList` when two step functions agree on all fields in `fields`. -/
theorem decodeFieldList_congr
    (step1 step2 : Nat → TyLayout → Except DecodeError PureConst)
    (baseOffset : Nat) :
    ∀ (fields : List (Nat × TyLayout)),
      (∀ relOff fLayout, (relOff, fLayout) ∈ fields →
        step1 (baseOffset + relOff) fLayout = step2 (baseOffset + relOff) fLayout) →
      decodeFieldList step1 baseOffset fields = decodeFieldList step2 baseOffset fields
  | [], _ => rfl
  | (relOff, fLayout) :: rest, h => by
    simp only [decodeFieldList]
    have hHead : step1 (baseOffset + relOff) fLayout = step2 (baseOffset + relOff) fLayout :=
      h relOff fLayout (.head _)
    have hTail : decodeFieldList step1 baseOffset rest = decodeFieldList step2 baseOffset rest :=
      decodeFieldList_congr step1 step2 baseOffset rest
        (fun r fl hMem => h r fl (.tail _ hMem))
    rw [hHead, hTail]

/-- Congruence of `decodeStrideList` when two step functions agree at all element offsets. -/
theorem decodeStrideList_congr
    (step1 step2 : Nat → TyLayout → Except DecodeError PureConst)
    (baseOffset : Nat) (elemTy : TyLayout) (elemStride : Nat) :
    ∀ (count : Nat),
      (∀ i < count,
        step1 (baseOffset + i * elemStride) elemTy =
          step2 (baseOffset + i * elemStride) elemTy) →
      decodeStrideList step1 baseOffset elemTy elemStride count =
        decodeStrideList step2 baseOffset elemTy elemStride count
  | 0, _ => rfl
  | k + 1, h => by
    simp only [decodeStrideList]
    have h0 : step1 baseOffset elemTy = step2 baseOffset elemTy := by
      have := h 0 (Nat.zero_lt_succ k)
      simpa [Nat.zero_mul, Nat.add_zero] using this
    have hk :
        decodeStrideList step1 (baseOffset + elemStride) elemTy elemStride k =
          decodeStrideList step2 (baseOffset + elemStride) elemTy elemStride k := by
      apply decodeStrideList_congr step1 step2 (baseOffset + elemStride) elemTy elemStride k
      intro i hi
      have := h (i + 1) (Nat.succ_lt_succ hi)
      have hArith : baseOffset + elemStride + i * elemStride = baseOffset + (i + 1) * elemStride := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm elemStride (i * elemStride)]
      rw [hArith]
      exact this
    rw [h0, hk]

/-- Two allocations agree on the byte window `[off, off + width)`. -/
structure AllocAgreeOnWindow (a1 a2 : Allocation) (off width : Nat) : Prop where
  len_eq : a1.bytes.length = a2.bytes.length
  bytes_eq : ∀ i < width, a1.bytes.getD (off + i) 0 = a2.bytes.getD (off + i) 0
  init_eq : ∀ i < width, checkInitByte a1.initMask (off + i) = checkInitByte a2.initMask (off + i)
  prov_eq : a1.provenance = a2.provenance

/-- Window agreement implies `decodeFromAlloc` produces the exact same `PureConst` on any integer
field, regardless of uninitialized or mutated padding bytes outside `[off, off + bits / 8)`. -/
theorem decodeFromAlloc_int_window_congr
    (env : AllocEnv) (fuel : Nat) (a1 a2 : Allocation) (off bits : Nat) (signed : Bool)
    (hAgree : AllocAgreeOnWindow a1 a2 off (bits / 8)) :
    decodeFromAlloc env (fuel + 1) a1 off (.int bits signed) =
      decodeFromAlloc env (fuel + 1) a2 off (.int bits signed) := by
  dsimp only [decodeFromAlloc, decodeIntLeaf]
  rw [hAgree.len_eq, hAgree.prov_eq]
  rw [checkInitRangeBytes_congr a1.initMask a2.initMask off (bits / 8) hAgree.init_eq]
  rw [readLeBytes_congr a1.bytes a2.bytes off (bits / 8) hAgree.bytes_eq]

/-- Window agreement implies `decodeFromAlloc` produces the exact same `PureConst` on any boolean
field, regardless of uninitialized or mutated padding bytes outside `[off, off + 1)`. -/
theorem decodeFromAlloc_bool_window_congr
    (env : AllocEnv) (fuel : Nat) (a1 a2 : Allocation) (off : Nat)
    (hAgree : AllocAgreeOnWindow a1 a2 off 1) :
    decodeFromAlloc env (fuel + 1) a1 off .bool =
      decodeFromAlloc env (fuel + 1) a2 off .bool := by
  dsimp only [decodeFromAlloc, decodeBoolLeaf]
  rw [hAgree.len_eq, hAgree.prov_eq]
  rw [checkInitRangeBytes_congr a1.initMask a2.initMask off 1 hAgree.init_eq]
  have hByte0 : a1.bytes.getD off 0 = a2.bytes.getD off 0 := by
    have := hAgree.bytes_eq 0 (Nat.zero_lt_one)
    simpa [Nat.add_zero] using this
  rw [hByte0]

/-- **Theorem 1a (Padding-Byte & Uninit-Gap Invariance on `Allocation`)**:
If two allocations `a1` and `a2` have the same total byte length and agree on decoding each
field `(relOff, fLayout)` of a struct (even if `a1` has `init = false` at padding gaps and `a2`
has arbitrary initialized bytes such as `0xAA` at padding gaps), `decodeFromAlloc` produces the
exact same `PureConst`. -/
theorem decodeFromAlloc_struct_padding_invariant
    (env : AllocEnv) (fuel : Nat) (a1 a2 : Allocation) (baseOffset : Nat)
    (adtId : AdtId) (fields : List (Nat × TyLayout)) (totalSize : Nat)
    (hLen : a1.bytes.length = a2.bytes.length)
    (hFields : ∀ relOff fLayout, (relOff, fLayout) ∈ fields →
      decodeFromAlloc env fuel a1 (baseOffset + relOff) fLayout =
        decodeFromAlloc env fuel a2 (baseOffset + relOff) fLayout) :
    decodeFromAlloc env (fuel + 1) a1 baseOffset (.struct adtId fields totalSize) =
      decodeFromAlloc env (fuel + 1) a2 baseOffset (.struct adtId fields totalSize) := by
  dsimp only [decodeFromAlloc]
  rw [hLen, decodeFieldList_congr (decodeFromAlloc env fuel a1) (decodeFromAlloc env fuel a2)
        baseOffset fields hFields]

/-- **Theorem 1b (Padding-Byte & Uninit-Gap Invariance on `decodeAllocAt`)**:
If `env1 allocId = some (.memory a1)` and `env2 allocId = some (.memory a2)` where `a1` and `a2`
have the same length and agree on the struct's fields at `fuel`, `decodeAllocAt` produces the
exact same `PureConst` regardless of padding bytes and padding `InitMask` bits. -/
theorem decodeAllocAt_struct_padding_invariant
    (env1 env2 : AllocEnv) (fuel : Nat) (allocId : AllocId)
    (a1 a2 : Allocation) (baseOffset : Nat)
    (adtId : AdtId) (fields : List (Nat × TyLayout)) (totalSize : Nat)
    (hEnv1 : env1 allocId = some (.memory a1))
    (hEnv2 : env2 allocId = some (.memory a2))
    (hLen : a1.bytes.length = a2.bytes.length)
    (hFields : ∀ relOff fLayout, (relOff, fLayout) ∈ fields →
      decodeFromAlloc env1 fuel a1 (baseOffset + relOff) fLayout =
        decodeFromAlloc env2 fuel a2 (baseOffset + relOff) fLayout) :
    decodeAllocAt env1 (fuel + 1) allocId baseOffset (.struct adtId fields totalSize) =
      decodeAllocAt env2 (fuel + 1) allocId baseOffset (.struct adtId fields totalSize) := by
  dsimp only [decodeAllocAt, lookupMemoryAlloc]
  rw [hEnv1, hEnv2]
  dsimp only [bind, Except.bind, decodeFromAlloc]
  rw [hLen, decodeFieldList_congr (decodeFromAlloc env1 fuel a1) (decodeFromAlloc env2 fuel a2)
        baseOffset fields hFields]

/-! ### Theorem 2: `AllocId` Bijection / Address-Independence Invariance -/

/-- Rename `AllocId` inside a `ProvPtr`. -/
def remapProvPtr (π : AllocId → AllocId) (p : ProvPtr) : ProvPtr :=
  { allocId := π p.allocId, offset := p.offset }

/-- Rename `AllocId`s across a `ProvenanceMap`. -/
def remapProvenanceMap (π : AllocId → AllocId) : ProvenanceMap → ProvenanceMap
  | [] => []
  | (off, ptr) :: rest => (off, remapProvPtr π ptr) :: remapProvenanceMap π rest

/-- Rename `AllocId`s inside an `Allocation`'s provenance map. -/
def remapAllocation (π : AllocId → AllocId) (a : Allocation) : Allocation :=
  { a with provenance := remapProvenanceMap π a.provenance }

@[simp] theorem remapAllocation_bytes (π : AllocId → AllocId) (a : Allocation) :
    (remapAllocation π a).bytes = a.bytes := rfl

@[simp] theorem remapAllocation_initMask (π : AllocId → AllocId) (a : Allocation) :
    (remapAllocation π a).initMask = a.initMask := rfl

@[simp] theorem remapAllocation_provenance (π : AllocId → AllocId) (a : Allocation) :
    (remapAllocation π a).provenance = remapProvenanceMap π a.provenance := rfl

/-- Rename `AllocId`s inside a `GlobalAlloc`. -/
def remapGlobalAlloc (π : AllocId → AllocId) : GlobalAlloc → GlobalAlloc
  | .memory a => .memory (remapAllocation π a)
  | .staticDef d => .staticDef d
  | .fnPtr f => .fnPtr f

/-- Rename `AllocId`s inside a `ScalarVal`. -/
def remapScalarVal (π : AllocId → AllocId) : ScalarVal → ScalarVal
  | .int v sz => .int v sz
  | .ptr p sz => .ptr (remapProvPtr π p) sz

/-- Rename `AllocId`s inside a `ConstValue`. -/
def remapCV (π : AllocId → AllocId) : ConstValue → ConstValue
  | .zeroSized => .zeroSized
  | .scalar s => .scalar (remapScalarVal π s)
  | .slice id len => .slice (π id) len
  | .indirect id off => .indirect (π id) off

theorem hasProvenanceInRange_remap (π : AllocId → AllocId) (prov : ProvenanceMap)
    (baseOffset byteWidth : Nat) :
    hasProvenanceInRange (remapProvenanceMap π prov) baseOffset byteWidth =
      hasProvenanceInRange prov baseOffset byteWidth := by
  induction prov with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨off, ptr⟩
    dsimp only [remapProvenanceMap, hasProvenanceInRange]
    rw [ih]

theorem noProvenanceInRange_remap (π : AllocId → AllocId) (prov : ProvenanceMap)
    (baseOffset byteWidth : Nat) :
    noProvenanceInRange (remapProvenanceMap π prov) baseOffset byteWidth =
      noProvenanceInRange prov baseOffset byteWidth := by
  dsimp only [noProvenanceInRange]
  rw [hasProvenanceInRange_remap]

theorem lookupProvenanceAt_remap (π : AllocId → AllocId) (prov : ProvenanceMap) (offset : Nat) :
    lookupProvenanceAt (remapProvenanceMap π prov) offset =
      (lookupProvenanceAt prov offset).map (remapProvPtr π) := by
  induction prov with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨off, ptr⟩
    dsimp only [remapProvenanceMap, lookupProvenanceAt]
    cases off == offset
    · exact ih
    · rfl

theorem lookupExactProvenance_remap (π : AllocId → AllocId) (prov : ProvenanceMap)
    (baseOffset ptrByteWidth : Nat) :
    lookupExactProvenance (remapProvenanceMap π prov) baseOffset ptrByteWidth =
      (lookupExactProvenance prov baseOffset ptrByteWidth).map (remapProvPtr π) := by
  dsimp only [lookupExactProvenance]
  rw [noProvenanceInRange_remap, lookupProvenanceAt_remap]
  cases noProvenanceInRange prov (baseOffset + 1) (ptrByteWidth - 1) <;> rfl

theorem decodeBoolLeaf_remap (π : AllocId → AllocId) (alloc : Allocation) (baseOffset : Nat) :
    decodeBoolLeaf (remapAllocation π alloc) baseOffset = decodeBoolLeaf alloc baseOffset := by
  dsimp only [decodeBoolLeaf]
  rw [remapAllocation_bytes, remapAllocation_initMask, remapAllocation_provenance,
    noProvenanceInRange_remap]

theorem decodeIntLeaf_remap (π : AllocId → AllocId) (alloc : Allocation)
    (baseOffset bits : Nat) (signed : Bool) :
    decodeIntLeaf (remapAllocation π alloc) baseOffset bits signed =
      decodeIntLeaf alloc baseOffset bits signed := by
  dsimp only [decodeIntLeaf]
  rw [remapAllocation_bytes, remapAllocation_initMask, remapAllocation_provenance,
    noProvenanceInRange_remap]

theorem checkRefHeader_remap (π : AllocId → AllocId) (alloc : Allocation) (baseOffset : Nat) :
    checkRefHeader (remapAllocation π alloc) baseOffset =
      (checkRefHeader alloc baseOffset).map (remapProvPtr π) := by
  dsimp only [checkRefHeader]
  rw [remapAllocation_initMask, remapAllocation_provenance, lookupExactProvenance_remap]
  cases checkInitRangeBytes alloc.initMask baseOffset 8 with
  | true =>
    cases lookupExactProvenance alloc.provenance baseOffset 8 <;> rfl
  | false => rfl

theorem checkSliceRefHeader_remap (π : AllocId → AllocId) (alloc : Allocation) (baseOffset : Nat) :
    checkSliceRefHeader (remapAllocation π alloc) baseOffset =
      (checkSliceRefHeader alloc baseOffset).map (fun (ptr, len) => (remapProvPtr π ptr, len)) := by
  dsimp only [checkSliceRefHeader]
  rw [remapAllocation_bytes, remapAllocation_initMask, remapAllocation_provenance,
    noProvenanceInRange_remap, lookupExactProvenance_remap]
  cases checkInitRangeBytes alloc.initMask baseOffset 16 with
  | true =>
    cases noProvenanceInRange alloc.provenance (baseOffset + 8) 8 with
    | true =>
      cases lookupExactProvenance alloc.provenance baseOffset 8 <;> rfl
    | false => rfl
  | false => rfl

theorem decodeEnumVariantIdx_remap (π : AllocId → AllocId) (alloc : Allocation)
    (baseOffset : Nat) (tagEnc : EnumTagEncoding) :
    decodeEnumVariantIdx (remapAllocation π alloc) baseOffset tagEnc =
      decodeEnumVariantIdx alloc baseOffset tagEnc := by
  cases tagEnc with
  | single optIdx => rfl
  | directTag tagOff tagBits tagSigned discrs =>
    dsimp only [decodeEnumVariantIdx]
    rw [remapAllocation_bytes, remapAllocation_initMask, remapAllocation_provenance,
      noProvenanceInRange_remap]
  | nicheTag tagOff tagBits untaggedVar sVar eVar sVal =>
    dsimp only [decodeEnumVariantIdx]
    rw [remapAllocation_bytes, remapAllocation_initMask, remapAllocation_provenance,
      noProvenanceInRange_remap]

theorem lookupMemoryAlloc_remap (π : AllocId → AllocId) (env1 env2 : AllocEnv)
    (hEnv : ∀ id, env2 (π id) = (env1 id).map (remapGlobalAlloc π)) (id : AllocId) :
    lookupMemoryAlloc env2 (π id) = (lookupMemoryAlloc env1 id).map (remapAllocation π) := by
  dsimp only [lookupMemoryAlloc]
  rw [hEnv id]
  cases env1 id with
  | none => rfl
  | some g =>
    cases g <;> rfl

theorem scalarIntAllocation_remap (π : AllocId → AllocId) (raw sizeBytes : Nat) :
    remapAllocation π (scalarIntAllocation raw sizeBytes) = scalarIntAllocation raw sizeBytes := by
  rfl

/-- `decodeFromAlloc` is completely invariant under any `AllocId` renaming `π` that commutes with
environment lookup (`env2 (π id) = (env1 id).map (remapGlobalAlloc π)`). -/
theorem decodeFromAlloc_remap_invariant (π : AllocId → AllocId) (env1 env2 : AllocEnv)
    (hEnv : ∀ id, env2 (π id) = (env1 id).map (remapGlobalAlloc π))
    (fuel : Nat) :
    ∀ (alloc : Allocation) (baseOffset : Nat) (layout : TyLayout),
      decodeFromAlloc env2 fuel (remapAllocation π alloc) baseOffset layout =
        decodeFromAlloc env1 fuel alloc baseOffset layout := by
  induction fuel with
  | zero =>
    intro _ _ _
    rfl
  | succ fuel ih =>
    intro alloc baseOffset layout
    cases layout with
    | unit =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes]
    | bool =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes, decodeBoolLeaf_remap]
    | int bits signed =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes, decodeIntLeaf_remap]
    | tuple fields totalSize =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes,
          decodeFieldList_congr
            (decodeFromAlloc env2 fuel (remapAllocation π alloc))
            (decodeFromAlloc env1 fuel alloc)
            baseOffset fields
            (fun r fl _ => ih alloc (baseOffset + r) fl)]
    | struct adtId fields totalSize =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes,
          decodeFieldList_congr
            (decodeFromAlloc env2 fuel (remapAllocation π alloc))
            (decodeFromAlloc env1 fuel alloc)
            baseOffset fields
            (fun r fl _ => ih alloc (baseOffset + r) fl)]
    | array elemTy elemStride count =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes,
          decodeStrideList_congr
            (decodeFromAlloc env2 fuel (remapAllocation π alloc))
            (decodeFromAlloc env1 fuel alloc)
            baseOffset elemTy elemStride count
            (fun i _ => ih alloc (baseOffset + i * elemStride) elemTy)]
    | enumLayout adtId tagEnc variants totalSize =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes, decodeEnumVariantIdx_remap]
      cases decodeEnumVariantIdx alloc baseOffset tagEnc with
      | error _ => rfl
      | ok vIdx =>
        dsimp only [bind, Except.bind]
        cases findVariantFields variants vIdx with
        | none => rfl
        | some payloadFields =>
          dsimp only []
          rw [decodeFieldList_congr
                (decodeFromAlloc env2 fuel (remapAllocation π alloc))
                (decodeFromAlloc env1 fuel alloc)
                baseOffset payloadFields
                (fun r fl _ => ih alloc (baseOffset + r) fl)]
    | ref pointee =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes, checkRefHeader_remap]
      cases checkRefHeader alloc baseOffset with
      | error _ => rfl
      | ok ptr =>
        dsimp only [Except.map, bind, Except.bind, remapProvPtr]
        rw [lookupMemoryAlloc_remap π env1 env2 hEnv ptr.allocId]
        cases lookupMemoryAlloc env1 ptr.allocId with
        | error _ => rfl
        | ok targetAlloc =>
          dsimp only [Except.map, bind, Except.bind]
          rw [ih targetAlloc ptr.offset pointee]
    | sliceRef elemTy elemStride =>
      dsimp only [decodeFromAlloc]
      rw [remapAllocation_bytes, checkSliceRefHeader_remap]
      cases checkSliceRefHeader alloc baseOffset with
      | error _ => rfl
      | ok pair =>
        rcases pair with ⟨ptr, metaLen⟩
        dsimp only [Except.map, bind, Except.bind, remapProvPtr]
        rw [lookupMemoryAlloc_remap π env1 env2 hEnv ptr.allocId]
        cases lookupMemoryAlloc env1 ptr.allocId with
        | error _ => rfl
        | ok targetAlloc =>
          dsimp only [Except.map, bind, Except.bind]
          rw [decodeStrideList_congr
                (decodeFromAlloc env2 fuel (remapAllocation π targetAlloc))
                (decodeFromAlloc env1 fuel targetAlloc)
                ptr.offset elemTy elemStride metaLen
                (fun i _ => ih targetAlloc (ptr.offset + i * elemStride) elemTy)]

/-- `decodeAllocAt` is invariant under `AllocId` renaming `π`. -/
theorem decodeAllocAt_remap_invariant (π : AllocId → AllocId) (env1 env2 : AllocEnv)
    (hEnv : ∀ id, env2 (π id) = (env1 id).map (remapGlobalAlloc π))
    (fuel : Nat) (allocId : AllocId) (baseOffset : Nat) (layout : TyLayout) :
    decodeAllocAt env2 fuel (π allocId) baseOffset layout =
      decodeAllocAt env1 fuel allocId baseOffset layout := by
  dsimp only [decodeAllocAt]
  rw [lookupMemoryAlloc_remap π env1 env2 hEnv allocId]
  cases lookupMemoryAlloc env1 allocId with
  | error _ => rfl
  | ok alloc =>
    dsimp only [Except.map, bind, Except.bind]
    exact decodeFromAlloc_remap_invariant π env1 env2 hEnv fuel alloc baseOffset layout

/-- **Theorem 2 (`AllocId` Bijection / Address-Independence Invariance)**:
For any `AllocId` renaming `π : AllocId → AllocId` that preserves `AllocEnv` lookups
(`∀ id, env2 (π id) = (env1 id).map (remapGlobalAlloc π)`), decoding `remapCV π cv` in `env2`
produces the exact same `PureConst` as decoding `cv` in `env1`. -/
theorem decodeConstValue_remap_invariant (π : AllocId → AllocId) (env1 env2 : AllocEnv)
    (hEnv : ∀ id, env2 (π id) = (env1 id).map (remapGlobalAlloc π))
    (fuel : Nat) (cv : ConstValue) (layout : TyLayout) :
    decodeConstValue env2 fuel (remapCV π cv) layout =
      decodeConstValue env1 fuel cv layout := by
  cases cv with
  | zeroSized =>
    dsimp only [remapCV, decodeConstValue]
    have hScalar :=
      decodeFromAlloc_remap_invariant π env1 env2 hEnv fuel (scalarIntAllocation 0 0) 0 layout
    rw [scalarIntAllocation_remap] at hScalar
    rw [hScalar]
  | scalar s =>
    cases s with
    | int raw sizeBytes =>
      dsimp only [remapCV, remapScalarVal, decodeConstValue]
      have hScalar :=
        decodeFromAlloc_remap_invariant π env1 env2 hEnv fuel (scalarIntAllocation raw sizeBytes) 0 layout
      rw [scalarIntAllocation_remap] at hScalar
      rw [hScalar]
    | ptr target sizeBytes =>
      dsimp only [remapCV, remapScalarVal, remapProvPtr, decodeConstValue]
      cases layout <;> try rfl
      case ref pointee =>
        dsimp only []
        rw [decodeAllocAt_remap_invariant π env1 env2 hEnv fuel target.allocId target.offset pointee]
  | slice allocId metaLen =>
    dsimp only [remapCV, decodeConstValue]
    cases layout <;> try rfl
    case sliceRef elemTy elemStride =>
      cases fuel with
      | zero => rfl
      | succ fuel' =>
        dsimp only []
        rw [lookupMemoryAlloc_remap π env1 env2 hEnv allocId]
        cases lookupMemoryAlloc env1 allocId with
        | error _ => rfl
        | ok targetAlloc =>
          dsimp only [Except.map, bind, Except.bind]
          rw [remapAllocation_bytes,
              decodeStrideList_congr
                (decodeFromAlloc env2 fuel' (remapAllocation π targetAlloc))
                (decodeFromAlloc env1 fuel' targetAlloc)
                0 elemTy elemStride metaLen
                (fun i _ => decodeFromAlloc_remap_invariant π env1 env2 hEnv fuel' targetAlloc (0 + i * elemStride) elemTy)]
  | indirect allocId offset =>
    dsimp only [remapCV, decodeConstValue]
    exact decodeAllocAt_remap_invariant π env1 env2 hEnv fuel allocId offset layout

/-! ### Theorem 3: Provenance-Forgery Rejection -/

/-- **Theorem 3a (Provenance-Forgery Rejection for Integer Scalars)**:
If any byte within an integer field `[baseOffset, baseOffset + bits / 8)` carries pointer
provenance in `alloc.provenance`, `decodeAllocAt` fails closed with
`.error .unexpectedProvenanceInScalar`. -/
theorem decodeAllocAt_int_rejects_provenance
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset bits : Nat) (signed : Bool)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + bits / 8) = false)
    (hInit : checkInitRangeBytes alloc.initMask baseOffset (bits / 8) = true)
    (hProv : hasProvenanceInRange alloc.provenance baseOffset (bits / 8) = true) :
    decodeAllocAt env (fuel + 1) allocId baseOffset (.int bits signed) =
      .error .unexpectedProvenanceInScalar := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, decodeIntLeaf, TyLayout.byteSize, hBounds, hInit,
    noProvenanceInRange, hProv]

/-- **Theorem 3b (Provenance-Forgery Rejection for Bool Scalars)**:
If a boolean byte carries pointer provenance in `alloc.provenance`, `decodeAllocAt` fails closed
with `.error .unexpectedProvenanceInScalar`. -/
theorem decodeAllocAt_bool_rejects_provenance
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset : Nat)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + 1) = false)
    (hInit : checkInitRangeBytes alloc.initMask baseOffset 1 = true)
    (hProv : hasProvenanceInRange alloc.provenance baseOffset 1 = true) :
    decodeAllocAt env (fuel + 1) allocId baseOffset .bool =
      .error .unexpectedProvenanceInScalar := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, decodeBoolLeaf, TyLayout.byteSize, hBounds, hInit,
    noProvenanceInRange, hProv]

/-- **Theorem 3c (Provenance-Forgery Rejection for Direct-Tag Enum Discriminants)**:
If any byte within an enum's discriminant tag carries pointer provenance in `alloc.provenance`,
`decodeAllocAt` fails closed with `.error .unexpectedProvenanceInScalar`. -/
theorem decodeAllocAt_enum_tag_rejects_provenance
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset : Nat) (adtId : AdtId) (tagOff tagBits : Nat) (tagSigned : Bool)
    (discrs : List (Nat × Int)) (variants : List (Nat × List (Nat × TyLayout))) (totalSize : Nat)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + totalSize) = false)
    (hInit : checkInitRangeBytes alloc.initMask (baseOffset + tagOff) (tagBits / 8) = true)
    (hProv : hasProvenanceInRange alloc.provenance (baseOffset + tagOff) (tagBits / 8) = true) :
    decodeAllocAt env (fuel + 1) allocId baseOffset
      (.enumLayout adtId (.directTag tagOff tagBits tagSigned discrs) variants totalSize) =
      .error .unexpectedProvenanceInScalar := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, TyLayout.byteSize, hBounds, decodeEnumVariantIdx,
    hInit, noProvenanceInRange, hProv]

/-! ### Theorem 4: Uninitialized-Scalar Rejection -/

/-- **Theorem 4a (Uninitialized-Scalar Rejection for Integer Fields)**:
If any byte within `[baseOffset, baseOffset + bits / 8)` is uninitialized
(`checkInitRangeBytes alloc.initMask baseOffset (bits / 8) = false`), `decodeAllocAt` fails
closed with `.error .uninitializedBytes`. -/
theorem decodeAllocAt_int_rejects_uninit
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset bits : Nat) (signed : Bool)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + bits / 8) = false)
    (hUninit : checkInitRangeBytes alloc.initMask baseOffset (bits / 8) = false) :
    decodeAllocAt env (fuel + 1) allocId baseOffset (.int bits signed) =
      .error .uninitializedBytes := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, decodeIntLeaf, TyLayout.byteSize, hBounds, hUninit]

/-- **Theorem 4b (Uninitialized-Scalar Rejection for Bool Fields)**:
If a boolean byte has `checkInitRangeBytes alloc.initMask baseOffset 1 = false`, `decodeAllocAt`
fails closed with `.error .uninitializedBytes`. -/
theorem decodeAllocAt_bool_rejects_uninit
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset : Nat)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + 1) = false)
    (hUninit : checkInitRangeBytes alloc.initMask baseOffset 1 = false) :
    decodeAllocAt env (fuel + 1) allocId baseOffset .bool =
      .error .uninitializedBytes := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, decodeBoolLeaf, TyLayout.byteSize, hBounds, hUninit]

/-- **Theorem 4c (Uninitialized-Tag Rejection for Niche-Encoded Enums)**:
If any byte of a niche-encoded enum tag is uninitialized, `decodeAllocAt` fails closed with
`.error .uninitializedBytes`. -/
theorem decodeAllocAt_niche_tag_rejects_uninit
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset : Nat) (adtId : AdtId) (tagOff tagBits untaggedVar sVar eVar sVal : Nat)
    (variants : List (Nat × List (Nat × TyLayout))) (totalSize : Nat)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + totalSize) = false)
    (hUninit : checkInitRangeBytes alloc.initMask (baseOffset + tagOff) (tagBits / 8) = false) :
    decodeAllocAt env (fuel + 1) allocId baseOffset
      (.enumLayout adtId (.nicheTag tagOff tagBits untaggedVar sVar eVar sVal) variants totalSize) =
      .error .uninitializedBytes := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, TyLayout.byteSize, hBounds, decodeEnumVariantIdx, hUninit]

/-- **Theorem 4d (Uninitialized-Pointer Rejection for References)**:
If any byte of a reference pointer is uninitialized, `decodeAllocAt` fails closed with
`.error .uninitializedBytes`. -/
theorem decodeAllocAt_ref_rejects_uninit
    (env : AllocEnv) (fuel : Nat) (allocId : AllocId) (alloc : Allocation)
    (baseOffset : Nat) (pointee : TyLayout)
    (hEnv : env allocId = some (.memory alloc))
    (hBounds : Nat.blt alloc.bytes.length (baseOffset + 8) = false)
    (hUninit : checkInitRangeBytes alloc.initMask baseOffset 8 = false) :
    decodeAllocAt env (fuel + 1) allocId baseOffset (.ref pointee) =
      .error .uninitializedBytes := by
  simp [decodeAllocAt, lookupMemoryAlloc, hEnv, bind, Except.bind,
    decodeFromAlloc, checkRefHeader, TyLayout.byteSize, hBounds, hUninit]


/-! ## Section 4: Canonical Layout-Guided Encoder and Round-Trip Soundness (Theorem 5) -/

theorem writeLeBytes_length : ∀ (count val : Nat), (writeLeBytes val count).length = count
  | 0, _ => rfl
  | k + 1, val => by
    simp only [writeLeBytes, List.length_cons, writeLeBytes_length k (val / 256)]

theorem readLeBytes_cons_succ (b : Byte) (bs : List Byte) :
    ∀ (k offset : Nat), readLeBytes (b :: bs) (offset + 1) k = readLeBytes bs offset k
  | 0, _ => rfl
  | k + 1, offset => by
    simp only [readLeBytes, List.getD_cons_succ, readLeBytes_cons_succ b bs k (offset + 1)]

theorem readLeBytes_append_prefix :
    ∀ (pre suf : List Byte), readLeBytes (pre ++ suf) 0 pre.length = readLeBytes pre 0 pre.length
  | [], _ => rfl
  | b :: rest, suf => by
    simp only [List.cons_append, List.length_cons, readLeBytes, List.getD_cons_zero,
      readLeBytes_cons_succ, readLeBytes_append_prefix rest suf]

theorem readLeBytes_append_suffix :
    ∀ (pre suf : List Byte) (k offset : Nat),
      readLeBytes (pre ++ suf) (pre.length + offset) k = readLeBytes suf offset k
  | [], _, _, _ => by simp
  | b :: rest, suf, k, offset => by
    have hOff : (b :: rest).length + offset = (rest.length + offset) + 1 := by
      simp [Nat.add_right_comm, Nat.add_assoc]
    rw [List.cons_append, hOff, readLeBytes_cons_succ, readLeBytes_append_suffix rest suf k offset]

theorem uint8_ofNat_mod_toNat (val : Nat) : (UInt8.ofNat (val % 256)).toNat = val % 256 := by
  have hLt : val % 256 < 256 := Nat.mod_lt val (by decide)
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt hLt

theorem readLeBytes_writeLeBytes :
    ∀ (count val : Nat), readLeBytes (writeLeBytes val count) 0 count = val % (256 ^ count)
  | 0, val => by
    simp [readLeBytes, Nat.pow_zero, Nat.mod_one]
  | k + 1, val => by
    simp only [writeLeBytes, readLeBytes, List.getD_cons_zero,
      uint8_ofNat_mod_toNat, readLeBytes_cons_succ, readLeBytes_writeLeBytes k (val / 256)]
    have hPow : 256 ^ (k + 1) = 256 * 256 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow]
    exact Nat.mod_mul.symm

theorem readLeBytes_writeLeBytes_of_lt (count val : Nat) (hLt : val < 256 ^ count) :
    readLeBytes (writeLeBytes val count) 0 count = val := by
  rw [readLeBytes_writeLeBytes, Nat.mod_eq_of_lt hLt]

theorem checkInitRangeBytes_cons_succ (b : Bool) (bs : InitMask) :
    ∀ (k offset : Nat),
      checkInitRangeBytes (b :: bs) (offset + 1) k = checkInitRangeBytes bs offset k
  | 0, _ => rfl
  | k + 1, offset => by
    simp only [checkInitRangeBytes, checkInitByte, List.getD_cons_succ,
      checkInitRangeBytes_cons_succ b bs k (offset + 1)]

theorem checkInitRangeBytes_replicate_true :
    ∀ (count : Nat), checkInitRangeBytes (List.replicate count true) 0 count = true
  | 0 => rfl
  | k + 1 => by
    simp only [List.replicate_succ, checkInitRangeBytes, checkInitByte, List.getD_cons_zero,
      Bool.true_and, checkInitRangeBytes_cons_succ, checkInitRangeBytes_replicate_true k]

/-- **Theorem 5a (Symbolic Integer Scalar Round-Trip)**:
For any integer layout `.int bits signed` and unsigned bit-pattern `val < 256 ^ (bits / 8)`,
decoding `ConstValue.scalar (.int val (bits / 8))` recovers `.ok (.int bits signed val)`. -/
theorem decodeConstValue_scalar_int_roundtrip
    (env : AllocEnv) (fuel : Nat) (bits : Nat) (signed : Bool) (val : Nat)
    (hLt : val < 256 ^ (bits / 8)) :
    decodeConstValue env (fuel + 1) (.scalar (.int val (bits / 8))) (.int bits signed) =
      .ok (.int bits signed val) := by
  have hLen : (writeLeBytes val (bits / 8)).length = bits / 8 := writeLeBytes_length (bits / 8) val
  simp [decodeConstValue, decodeFromAlloc, decodeIntLeaf, scalarIntAllocation,
    TyLayout.byteSize, hLen, checkInitRangeBytes_replicate_true,
    noProvenanceInRange, hasProvenanceInRange, readLeBytes_writeLeBytes_of_lt (bits / 8) val hLt]

/-- **Theorem 5b (Symbolic Boolean Scalar Round-Trip)**:
For any `b : Bool`, decoding `ConstValue.scalar (.int (if b then 1 else 0) 1)` recovers
`.ok (.bool b)`. -/
theorem decodeConstValue_scalar_bool_roundtrip
    (env : AllocEnv) (fuel : Nat) (b : Bool) :
    decodeConstValue env (fuel + 1) (.scalar (.int (if b then 1 else 0) 1)) .bool =
      .ok (.bool b) := by
  cases b <;> rfl

/-- Write a list of initialized bytes into `(bytes, mask)` starting at `offset`. -/
def writeBytesAt (bytes : List Byte) (mask : InitMask) (offset : Nat) :
    List Byte → List Byte × InitMask
  | [] => (bytes, mask)
  | b :: rest =>
    writeBytesAt (bytes.set offset b) (mask.set offset true) (offset + 1) rest

/-- Write a list of initialized bytes into `alloc` at `offset`. -/
def writeAllocBytes (alloc : Allocation) (offset : Nat) (bs : List Byte) : Allocation :=
  let (bytes', mask') := writeBytesAt alloc.bytes alloc.initMask offset bs
  { alloc with bytes := bytes', initMask := mask' }

/-- Construct an uninitialized `Allocation` of `totalSize` bytes (`initMask = replicate totalSize false`). -/
def emptyUninitAlloc (totalSize : Nat) (align : Nat := 8) : Allocation :=
  { bytes := List.replicate totalSize 0
    initMask := List.replicate totalSize false
    provenance := []
    align := align }

/-- Convert a signed or unsigned discriminant `Int` into its `tagBits`-bit unsigned representation. -/
def fromSignedInt (bits : Nat) (dVal : Int) : Nat :=
  let modulus := 2 ^ bits
  if dVal ≥ 0 then
    dVal.toNat % modulus
  else
    (modulus - ((-dVal).toNat % modulus)) % modulus

/-- Look up the discriminant value of `variantIdx` in `discriminants : List (Nat × Int)`. -/
def findVariantDiscriminant : List (Nat × Int) → Nat → Option Int
  | [], _ => none
  | (vIdx, dVal) :: rest, targetIdx =>
    if vIdx == targetIdx then some dVal else findVariantDiscriminant rest targetIdx

/-- Encode an enum variant's discriminant or niche tag into `alloc` at `baseOffset`. -/
def encodeEnumTag (alloc : Allocation) (baseOffset : Nat) (variantIdx : Nat) :
    EnumTagEncoding → Option Allocation
  | .single optIdx =>
    match optIdx with
    | none => none
    | some vIdx => if vIdx == variantIdx then some alloc else none
  | .directTag tagOff tagBits _ discrs => do
    let dVal ← findVariantDiscriminant discrs variantIdx
    let rawTag := fromSignedInt tagBits dVal
    some (writeAllocBytes alloc (baseOffset + tagOff) (writeLeBytes rawTag (tagBits / 8)))
  | .nicheTag tagOff tagBits untaggedVar nicheStartVar nicheEndVar nicheStartVal =>
    if variantIdx == untaggedVar then
      some alloc
    else if nicheStartVar ≤ variantIdx && variantIdx ≤ nicheEndVar then
      let modulus := 2 ^ tagBits
      let rawTag := (nicheStartVal + (variantIdx - nicheStartVar)) % modulus
      some (writeAllocBytes alloc (baseOffset + tagOff) (writeLeBytes rawTag (tagBits / 8)))
    else
      none

/-- Encode a list of `(relOffset, fieldLayout)` pairs and `PureConst` field values using `step`. -/
def encodeFieldList
    (step : Allocation → Nat → TyLayout → PureConst → Option Allocation)
    (alloc : Allocation) (baseOffset : Nat) :
    List (Nat × TyLayout) → List PureConst → Option Allocation
  | [], [] => some alloc
  | (relOff, fLayout) :: fRest, v :: vRest => do
    let alloc' ← step alloc (baseOffset + relOff) fLayout v
    encodeFieldList step alloc' baseOffset fRest vRest
  | _, _ => none

/-- Encode homogeneous array elements at stride `elemStride` starting at `baseOffset`. -/
def encodeStrideList
    (step : Allocation → Nat → TyLayout → PureConst → Option Allocation)
    (alloc : Allocation) (baseOffset : Nat) (elemTy : TyLayout) (elemStride : Nat) :
    Nat → List PureConst → Option Allocation
  | 0, [] => some alloc
  | k + 1, v :: vRest => do
    let alloc' ← step alloc baseOffset elemTy v
    encodeStrideList step alloc' (baseOffset + elemStride) elemTy elemStride k vRest
  | _, _ => none

/-- Canonical layout-guided encoder writing a `PureConst` into `alloc` at `baseOffset`.
Leaves all padding bytes between struct fields and in unused enum variant tails untouched
(preserving `initMask = false` when starting from `emptyUninitAlloc`). -/
def encodeToAllocAt : Nat → Allocation → Nat → TyLayout → PureConst → Option Allocation
  | 0, _, _, _, _ => none
  | fuel + 1, alloc, baseOffset, layout, c =>
    if Nat.blt alloc.bytes.length (baseOffset + layout.byteSize) then
      none
    else
      match layout, c with
      | .unit, .unit => some alloc
      | .bool, .bool b =>
        let byteVal : Byte := if b then 1 else 0
        some (writeAllocBytes alloc baseOffset [byteVal])
      | .int bits signed, .int bits' signed' val =>
        if bits == bits' && signed == signed' then
          some (writeAllocBytes alloc baseOffset (writeLeBytes val (bits / 8)))
        else
          none
      | .tuple fields _, .tuple vals =>
        encodeFieldList (encodeToAllocAt fuel) alloc baseOffset fields vals
      | .struct adtId fields _, .struct adtId' vals =>
        if adtId == adtId' then
          encodeFieldList (encodeToAllocAt fuel) alloc baseOffset fields vals
        else
          none
      | .array elemTy elemStride count, .array vals =>
        encodeStrideList (encodeToAllocAt fuel) alloc baseOffset elemTy elemStride count vals
      | .enumLayout adtId tagEnc variants _, .enumVariant adtId' vIdx payloadVals =>
        if adtId == adtId' then do
          let allocTag ← encodeEnumTag alloc baseOffset vIdx tagEnc
          let payloadFields ← findVariantFields variants vIdx
          encodeFieldList (encodeToAllocAt fuel) allocTag baseOffset payloadFields payloadVals
        else
          none
      | _, _ => none

/-- Ensure an encoded pure value allocation carries no raw pointer provenance. -/
def stripProvenance (alloc : Allocation) : Allocation :=
  { alloc with provenance := [] }

/-- If `alloc.provenance = []`, `decodeFromAlloc` does not inspect `env` (since `.ref` and
`.sliceRef` require provenance in `alloc` before looking up any pointee in `env`). -/
theorem decodeFromAlloc_env_irrel_of_no_provenance (env1 env2 : AllocEnv) :
    ∀ (fuel : Nat) (alloc : Allocation) (_hProv : alloc.provenance = [])
      (baseOffset : Nat) (layout : TyLayout),
      decodeFromAlloc env1 fuel alloc baseOffset layout =
        decodeFromAlloc env2 fuel alloc baseOffset layout
  | 0, _, _, _, _ => rfl
  | fuel + 1, alloc, hProv, baseOffset, layout => by
    have hStep :
        ∀ (off : Nat) (ly : TyLayout),
          decodeFromAlloc env1 fuel alloc off ly = decodeFromAlloc env2 fuel alloc off ly :=
      fun off ly => decodeFromAlloc_env_irrel_of_no_provenance env1 env2 fuel alloc hProv off ly
    unfold decodeFromAlloc
    split
    · rfl
    · cases layout with
      | unit => rfl
      | bool => rfl
      | int bits signed => rfl
      | tuple fields totalSize =>
        dsimp only []
        rw [decodeFieldList_congr (decodeFromAlloc env1 fuel alloc) (decodeFromAlloc env2 fuel alloc)
          baseOffset fields (fun off ly _ => hStep (baseOffset + off) ly)]
      | struct adtId fields totalSize =>
        dsimp only []
        rw [decodeFieldList_congr (decodeFromAlloc env1 fuel alloc) (decodeFromAlloc env2 fuel alloc)
          baseOffset fields (fun off ly _ => hStep (baseOffset + off) ly)]
      | array elemTy elemStride count =>
        dsimp only []
        rw [decodeStrideList_congr (decodeFromAlloc env1 fuel alloc) (decodeFromAlloc env2 fuel alloc)
          baseOffset elemTy elemStride count (fun i _ => hStep (baseOffset + i * elemStride) elemTy)]
      | enumLayout adtId tagEnc variants totalSize =>
        dsimp only []
        cases decodeEnumVariantIdx alloc baseOffset tagEnc with
        | error e => rfl
        | ok vIdx =>
          dsimp only [bind, Except.bind]
          cases findVariantFields variants vIdx with
          | none => rfl
          | some payloadFields =>
            dsimp only []
            rw [decodeFieldList_congr (decodeFromAlloc env1 fuel alloc) (decodeFromAlloc env2 fuel alloc)
              baseOffset payloadFields (fun off ly _ => hStep (baseOffset + off) ly)]
      | ref pointeeLayout =>
        dsimp only [checkRefHeader, bind, Except.bind]
        rw [hProv]
        dsimp only [lookupExactProvenance, lookupProvenanceAt]
        cases checkInitRangeBytes alloc.initMask baseOffset 8 <;> rfl
      | sliceRef elemLayout elemStride =>
        dsimp only [checkSliceRefHeader, bind, Except.bind]
        rw [hProv]
        dsimp only [lookupExactProvenance, lookupProvenanceAt, noProvenanceInRange, hasProvenanceInRange, Bool.false_eq_true, ↓reduceIte]
        cases checkInitRangeBytes alloc.initMask baseOffset 16 <;> rfl

/-- Encode a `PureConst` of `layout` into a standalone `Allocation` (with uninitialized padding). -/
def encodePureConstToAlloc (fuel : Nat) (layout : TyLayout) (c : PureConst) (align : Nat := 8) :
    Option Allocation :=
  (encodeToAllocAt fuel (emptyUninitAlloc layout.byteSize align) 0 layout c).map stripProvenance

/-- Bind a single `AllocId` to `GlobalAlloc.memory alloc` in a fresh `AllocEnv`. -/
def singleAllocEnv (allocId : AllocId) (alloc : Allocation) : AllocEnv :=
  fun id => if id == allocId then some (.memory alloc) else none

/-- Encode a `PureConst` into a canonical `(AllocEnv × ConstValue)` pair at `allocId`. -/
def encodePureConst (fuel : Nat) (allocId : AllocId) (layout : TyLayout) (c : PureConst) :
    Option (AllocEnv × ConstValue) := do
  let alloc ← encodePureConstToAlloc fuel layout c
  some (singleAllocEnv allocId alloc, .indirect allocId 0)

/-- Round-trip helper executing `encodePureConst` followed by `decodeConstValue`. -/
def encodeDecodeRoundtrip (fuel : Nat) (allocId : AllocId) (layout : TyLayout) (c : PureConst) :
    Option (Except DecodeError PureConst) := do
  let (env, cv) ← encodePureConst fuel allocId layout c
  some (decodeConstValue env fuel cv layout)

/-! ### Golden Case 5.1: Starnix `U64Range { min: 0, max: u64::MAX }` (16 bytes) -/

def u64Max : Nat := 0xffffffffffffffff

def u64Layout : TyLayout := .int 64 false
def u32Layout : TyLayout := .int 32 false
def u8Layout : TyLayout := .int 8 false

def u64RangeAdtId : AdtId := 1993

/-- Layout of `scalar_value::U64Range { min: u64, max: u64 }` (16 bytes, align 8). -/
def u64RangeLayout : TyLayout :=
  .struct u64RangeAdtId [(0, u64Layout), (8, u64Layout)] 16

def u64RangePure (minVal maxVal : Nat) : PureConst :=
  .struct u64RangeAdtId [.int 64 false minVal, .int 64 false maxVal]

def u64RangeMaxPure : PureConst :=
  u64RangePure 0 u64Max

/-- Symbolic 16-byte allocation for `U64Range { min: minVal, max: maxVal }`. -/
def u64RangeSymbolicAlloc (minVal maxVal : Nat) : Allocation :=
  { bytes := writeLeBytes minVal 8 ++ writeLeBytes maxVal 8
    initMask := List.replicate 16 true
    provenance := []
    align := 8 }

/-- **Theorem 5.1a (Concrete Starnix `U64Range::MAX` Round-Trip)**: -/
theorem u64RangeMax_encode_decode_roundtrip :
    encodeDecodeRoundtrip 4 1 u64RangeLayout u64RangeMaxPure = some (.ok u64RangeMaxPure) := by
  rfl

/-- **Theorem 5.1b (Symbolic `U64Range { min, max }` Round-Trip)**:
For ANY `minVal, maxVal < 256 ^ 8`, decoding `u64RangeSymbolicAlloc minVal maxVal` at `u64RangeLayout`
recovers `.ok (u64RangePure minVal maxVal)`. -/
theorem u64Range_symbolic_roundtrip (env : AllocEnv) (allocId : AllocId) (minVal maxVal : Nat)
    (hEnv : env allocId = some (.memory (u64RangeSymbolicAlloc minVal maxVal)))
    (hMin : minVal < 256 ^ 8) (hMax : maxVal < 256 ^ 8) :
    decodeConstValue env 2 (.indirect allocId 0) u64RangeLayout =
      .ok (u64RangePure minVal maxVal) := by
  have hLenMin : (writeLeBytes minVal 8).length = 8 := writeLeBytes_length 8 minVal
  have hLenMax : (writeLeBytes maxVal 8).length = 8 := writeLeBytes_length 8 maxVal
  have hLenTot : (writeLeBytes minVal 8 ++ writeLeBytes maxVal 8).length = 16 := by
    rw [List.length_append, hLenMin, hLenMax]
  have hRead0 :
      readLeBytes (writeLeBytes minVal 8 ++ writeLeBytes maxVal 8) 0 8 = minVal := by
    have hPre := readLeBytes_append_prefix (writeLeBytes minVal 8) (writeLeBytes maxVal 8)
    rw [hLenMin] at hPre
    rw [hPre, readLeBytes_writeLeBytes_of_lt 8 minVal hMin]
  have hRead8 :
      readLeBytes (writeLeBytes minVal 8 ++ writeLeBytes maxVal 8) 8 8 = maxVal := by
    have hSuf := readLeBytes_append_suffix (writeLeBytes minVal 8) (writeLeBytes maxVal 8) 8 0
    rw [hLenMin, Nat.add_zero] at hSuf
    rw [hSuf, readLeBytes_writeLeBytes_of_lt 8 maxVal hMax]
  dsimp only [decodeConstValue, decodeAllocAt, lookupMemoryAlloc]
  rw [hEnv]
  dsimp only [bind, Except.bind, decodeFromAlloc, decodeFieldList, decodeIntLeaf,
    u64RangeLayout, u64Layout, u64RangeSymbolicAlloc, u64RangePure, TyLayout.byteSize]
  rw [hLenTot, hRead0, hRead8]
  rfl

/-! ### Golden Case 5.2: Starnix `U64ScalarValueData::UNINITIALIZED` (40 bytes) -/

def u64ScalarValueDataAdtId : AdtId := 2060

/-- Layout of `scalar_value::U64ScalarValueData` (40 bytes, with nested `U64Range` at offset 24
and 0-sized `_guard: ()` at offset 40). -/
def u64ScalarValueDataLayout : TyLayout :=
  .struct u64ScalarValueDataAdtId
    [(0, u64Layout), (8, u64Layout), (16, u64Layout), (24, u64RangeLayout), (40, .unit)] 40

def u64ScalarValueDataUninitPure : PureConst :=
  .struct u64ScalarValueDataAdtId
    [.int 64 false 0, .int 64 false u64Max, .int 64 false u64Max, u64RangeMaxPure, .unit]

/-- **Theorem 5.2 (Starnix `U64ScalarValueData::UNINITIALIZED` 40-Byte Round-Trip)**: -/
theorem u64ScalarValueDataUninit_encode_decode_roundtrip :
    encodeDecodeRoundtrip 5 2 u64ScalarValueDataLayout u64ScalarValueDataUninitPure =
      some (.ok u64ScalarValueDataUninitPure) := by
  rfl

/-! ### Golden Case 5.3: Padded Struct `(u8, u32)` (8 bytes, 3 uninitialized padding bytes at 1..3) -/

def paddedU8U32AdtId : AdtId := 3001

def paddedU8U32Layout : TyLayout :=
  .struct paddedU8U32AdtId [(0, u8Layout), (4, u32Layout)] 8

def paddedU8U32Pure (v0 v1 : Nat) : PureConst :=
  .struct paddedU8U32AdtId [.int 8 false v0, .int 32 false v1]

/-- **Theorem 5.3a (Encoder Preserves Uninitialized Padding Gaps at Offsets `1..3`)**: -/
theorem paddedU8U32_initMask_has_uninit_gaps :
    (encodePureConstToAlloc 4 paddedU8U32Layout (paddedU8U32Pure 0x2A 0x12345678)).map (·.initMask) =
      some [true, false, false, false, true, true, true, true] := by
  rfl

/-- **Theorem 5.3b (Concrete Round-Trip with Uninitialized Padding Bytes)**: -/
theorem paddedU8U32_encode_decode_roundtrip :
    encodeDecodeRoundtrip 4 3 paddedU8U32Layout (paddedU8U32Pure 0x2A 0x12345678) =
      some (.ok (paddedU8U32Pure 0x2A 0x12345678)) := by
  rfl

/-- Symbolic 8-byte allocation for `(u8, u32)` with arbitrary padding bytes `p1, p2, p3` and
arbitrary padding initialization bits `i1, i2, i3` at offsets `1..3`. -/
def paddedU8U32SymbolicAlloc (v0 v1 : Nat) (p1 p2 p3 : Byte) (i1 i2 i3 : Bool) : Allocation :=
  { bytes := [UInt8.ofNat (v0 % 256), p1, p2, p3] ++ writeLeBytes v1 4
    initMask := [true, i1, i2, i3, true, true, true, true]
    provenance := []
    align := 4 }

/-- **Theorem 5.3c (Symbolic Round-Trip & Padding/InitMask Invariance for Padded `(u8, u32)`)**: -/
theorem paddedU8U32_symbolic_roundtrip
    (env : AllocEnv) (allocId : AllocId) (v0 v1 : Nat)
    (p1 p2 p3 : Byte) (i1 i2 i3 : Bool)
    (hEnv : env allocId = some (.memory (paddedU8U32SymbolicAlloc v0 v1 p1 p2 p3 i1 i2 i3)))
    (h0 : v0 < 256) (h1 : v1 < 256 ^ 4) :
    decodeConstValue env 2 (.indirect allocId 0) paddedU8U32Layout =
      .ok (paddedU8U32Pure v0 v1) := by
  have hLen4 : (writeLeBytes v1 4).length = 4 := writeLeBytes_length 4 v1
  have hLenTot : ([UInt8.ofNat (v0 % 256), p1, p2, p3] ++ writeLeBytes v1 4).length = 8 := by
    simp [hLen4]
  have hRead0 :
      readLeBytes ([UInt8.ofNat (v0 % 256), p1, p2, p3] ++ writeLeBytes v1 4) 0 1 = v0 := by
    simp [readLeBytes, Nat.mod_eq_of_lt h0]
  have hRead4 :
      readLeBytes ([UInt8.ofNat (v0 % 256), p1, p2, p3] ++ writeLeBytes v1 4) 4 4 = v1 := by
    have hSuf :=
      readLeBytes_append_suffix [UInt8.ofNat (v0 % 256), p1, p2, p3] (writeLeBytes v1 4) 4 0
    simpa [readLeBytes_writeLeBytes_of_lt 4 v1 h1] using hSuf
  dsimp only [decodeConstValue, decodeAllocAt, lookupMemoryAlloc]
  rw [hEnv]
  dsimp only [bind, Except.bind, decodeFromAlloc, decodeFieldList, decodeIntLeaf,
    paddedU8U32Layout, u8Layout, u32Layout, paddedU8U32SymbolicAlloc, paddedU8U32Pure,
    TyLayout.byteSize]
  rw [hLenTot, hRead0, hRead4]
  rfl

/-- **Theorem 5.3d (Concrete Uninit-Padding vs. `0xAA`-Initialized-Padding Equality)**:
Two allocations for `(u8, u32)`—one with uninitialized `0x00` padding at `1..3` (`init = false`)
and one with initialized `0xAA` padding at `1..3` (`init = true`)—decode to the exact same
`PureConst`. -/
theorem paddedU8U32_uninit_vs_0xAA_eq (v0 v1 : Nat) (h0 : v0 < 256) (h1 : v1 < 256 ^ 4) :
    let aUninit := paddedU8U32SymbolicAlloc v0 v1 0x00 0x00 0x00 false false false
    let aInitAA := paddedU8U32SymbolicAlloc v0 v1 0xAA 0xAA 0xAA true true true
    decodeConstValue (singleAllocEnv 1 aUninit) 2 (.indirect 1 0) paddedU8U32Layout =
      decodeConstValue (singleAllocEnv 1 aInitAA) 2 (.indirect 1 0) paddedU8U32Layout := by
  intro aUninit aInitAA
  have hL :=
    paddedU8U32_symbolic_roundtrip (singleAllocEnv 1 aUninit) 1 v0 v1 0 0 0 false false false rfl h0 h1
  have hR :=
    paddedU8U32_symbolic_roundtrip (singleAllocEnv 1 aInitAA) 1 v0 v1 0xAA 0xAA 0xAA true true true rfl h0 h1
  rw [hL, hR]

/-! ### Golden Case 5.4: Niche-Encoded `Option<bool>` and `Option<NonZeroU64>` -/

def optionBoolAdtId : AdtId := 4001

def optionBoolLayout : TyLayout :=
  .enumLayout optionBoolAdtId
    (.nicheTag 0 8 1 0 0 2)
    [(0, []), (1, [(0, .bool)])]
    1

def optionBoolNone : PureConst := .enumVariant optionBoolAdtId 0 []
def optionBoolSome (b : Bool) : PureConst := .enumVariant optionBoolAdtId 1 [.bool b]

theorem optionBool_none_roundtrip :
    encodeDecodeRoundtrip 4 4 optionBoolLayout optionBoolNone = some (.ok optionBoolNone) := by
  rfl

theorem optionBool_some_false_roundtrip :
    encodeDecodeRoundtrip 4 4 optionBoolLayout (optionBoolSome false) =
      some (.ok (optionBoolSome false)) := by
  rfl

theorem optionBool_some_true_roundtrip :
    encodeDecodeRoundtrip 4 4 optionBoolLayout (optionBoolSome true) =
      some (.ok (optionBoolSome true)) := by
  rfl

theorem optionBool_all_roundtrip (opt : Option Bool) :
    let c := match opt with | none => optionBoolNone | some b => optionBoolSome b
    encodeDecodeRoundtrip 4 4 optionBoolLayout c = some (.ok c) := by
  cases opt with
  | none => rfl
  | some b => cases b <;> rfl

theorem optionBool_invalid_byte_3_rejected (env : AllocEnv) :
    decodeConstValue env 3 (.scalar (.int 3 1)) optionBoolLayout =
      .error (.invalidBoolByte 3) := by
  rfl

/-- **Theorem 5.0a (Unit `encodeDecodeRoundtrip`)**: -/
theorem encodeDecodeRoundtrip_unit (allocId : AllocId) :
    encodeDecodeRoundtrip 2 allocId .unit .unit = some (.ok .unit) := by
  change some (do
    let alloc ← lookupMemoryAlloc (singleAllocEnv allocId (stripProvenance (emptyUninitAlloc 0 8))) allocId
    decodeFromAlloc (singleAllocEnv allocId (stripProvenance (emptyUninitAlloc 0 8))) 2 alloc 0 .unit) =
    some (.ok .unit)
  dsimp only [lookupMemoryAlloc, singleAllocEnv]
  rw [beq_self_eq_true]
  rfl

/-- **Theorem 5.0b (Symbolic Bool `encodeDecodeRoundtrip`)**: -/
theorem encodeDecodeRoundtrip_bool (allocId : AllocId) (b : Bool) :
    encodeDecodeRoundtrip 2 allocId .bool (.bool b) = some (.ok (.bool b)) := by
  cases b
  · change some (do
      let a0 := stripProvenance (writeAllocBytes (emptyUninitAlloc 1 8) 0 [0])
      let alloc ← lookupMemoryAlloc (singleAllocEnv allocId a0) allocId
      decodeFromAlloc (singleAllocEnv allocId a0) 2 alloc 0 .bool) = some (.ok (.bool false))
    dsimp only [lookupMemoryAlloc, singleAllocEnv]
    rw [beq_self_eq_true]
    rfl
  · change some (do
      let a1 := stripProvenance (writeAllocBytes (emptyUninitAlloc 1 8) 0 [1])
      let alloc ← lookupMemoryAlloc (singleAllocEnv allocId a1) allocId
      decodeFromAlloc (singleAllocEnv allocId a1) 2 alloc 0 .bool) = some (.ok (.bool true))
    dsimp only [lookupMemoryAlloc, singleAllocEnv]
    rw [beq_self_eq_true]
    rfl

/-- Niche-encoded `Result<bool, ()>` (`AdtId = 4003`, 1 byte):
- Variant `0` (`Ok(bool)`): untagged variant (`untaggedVar = 0`), payload `[(0, .bool)]` at offset `0` (`0 -> Ok(false)`, `1 -> Ok(true)`).
- Variant `1` (`Err(())`): niche variant (`nicheStartVar = 1, nicheEndVar = 1, nicheStartVal = 2`), payload `[(0, .unit)]` (`2 -> Err(())`). -/
def resultBoolUnitAdtId : AdtId := 4003

def resultBoolUnitLayout : TyLayout :=
  .enumLayout resultBoolUnitAdtId
    (.nicheTag 0 8 0 1 1 2)
    [(0, [(0, .bool)]), (1, [(0, .unit)])]
    1

def resultBoolUnitOk (b : Bool) : PureConst :=
  .enumVariant resultBoolUnitAdtId 0 [.bool b]

def resultBoolUnitErr : PureConst :=
  .enumVariant resultBoolUnitAdtId 1 [.unit]

/-- **Theorem 5.4b (Exhaustive `Result<bool, ()>` Niche Round-Trip)**: -/
theorem resultBoolUnit_all_roundtrip (res : Except Unit Bool) :
    let c := match res with | .ok b => resultBoolUnitOk b | .error () => resultBoolUnitErr
    encodeDecodeRoundtrip 4 6 resultBoolUnitLayout c = some (.ok c) := by
  cases res with
  | error u => cases u; rfl
  | ok b => cases b <;> rfl

def optionNonZeroU64AdtId : AdtId := 4002

def optionNonZeroU64Layout : TyLayout :=
  .enumLayout optionNonZeroU64AdtId
    (.nicheTag 0 64 1 0 0 0)
    [(0, []), (1, [(0, u64Layout)])]
    8

def optionNonZeroU64None : PureConst := .enumVariant optionNonZeroU64AdtId 0 []
def optionNonZeroU64Some (v : Nat) : PureConst :=
  .enumVariant optionNonZeroU64AdtId 1 [.int 64 false v]

theorem optionNonZeroU64_none_roundtrip :
    encodeDecodeRoundtrip 4 5 optionNonZeroU64Layout optionNonZeroU64None =
      some (.ok optionNonZeroU64None) := by
  rfl

theorem optionNonZeroU64_some_42_roundtrip :
    encodeDecodeRoundtrip 4 5 optionNonZeroU64Layout (optionNonZeroU64Some 42) =
      some (.ok (optionNonZeroU64Some 42)) := by
  rfl

theorem decodeEnumVariantIdx_optionNonZeroU64_some (v : Nat) (hPos : 0 < v) (hLt : v < 256 ^ 8) :
    decodeEnumVariantIdx (scalarIntAllocation v 8) 0 (.nicheTag 0 64 1 0 0 0) = .ok 1 := by
  have hRead : readLeBytes (writeLeBytes v 8) 0 8 = v := readLeBytes_writeLeBytes_of_lt 8 v hLt
  have hPow : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hMod : (v + 2 ^ 64 - 0 % 2 ^ 64) % 2 ^ 64 = v := by
    rw [hPow]
    omega
  have hBlt : Nat.blt v 1 = false := by
    cases v with
    | zero => omega
    | succ _ => rfl
  unfold decodeEnumVariantIdx scalarIntAllocation
  dsimp only [Nat.add_zero, Nat.reduceDiv]
  rw [hRead, hMod, hBlt]
  rfl

theorem decodeFromAlloc_int64_scalar (env : AllocEnv) (fuel : Nat) (v : Nat) (hLt : v < 256 ^ 8) :
    decodeFromAlloc env (fuel + 1) (scalarIntAllocation v 8) 0 u64Layout =
      .ok (.int 64 false v) := by
  have hLen : (scalarIntAllocation v 8).bytes.length = 8 := writeLeBytes_length 8 v
  have hRead : readLeBytes (scalarIntAllocation v 8).bytes 0 8 = v :=
    readLeBytes_writeLeBytes_of_lt 8 v hLt
  unfold decodeFromAlloc u64Layout decodeIntLeaf TyLayout.byteSize
  dsimp only [Nat.add_zero, Nat.reduceDiv]
  rw [hLen, hRead]
  rfl

/-- **Theorem 5.4c (Symbolic `Option<NonZeroU64>::Some(v)` Round-Trip for all `0 < v < 2^64`)**: -/
theorem optionNonZeroU64_some_symbolic_roundtrip
    (env : AllocEnv) (v : Nat) (hPos : 0 < v) (hLt : v < 256 ^ 8) :
    decodeConstValue env 2 (.scalar (.int v 8)) optionNonZeroU64Layout =
      .ok (optionNonZeroU64Some v) := by
  have hLen : (scalarIntAllocation v 8).bytes.length = 8 := writeLeBytes_length 8 v
  unfold decodeConstValue optionNonZeroU64Layout
  rw [show TyLayout.byteSize (.enumLayout optionNonZeroU64AdtId (.nicheTag 0 64 1 0 0 0) [(0, []), (1, [(0, u64Layout)])] 8) = 8 from rfl]
  dsimp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  unfold decodeFromAlloc
  rw [show TyLayout.byteSize (.enumLayout optionNonZeroU64AdtId (.nicheTag 0 64 1 0 0 0) [(0, []), (1, [(0, u64Layout)])] 8) = 8 from rfl]
  dsimp only [Nat.add_zero]
  rw [hLen, decodeEnumVariantIdx_optionNonZeroU64_some v hPos hLt]
  dsimp only [bind, Except.bind]
  rw [show findVariantFields [(0, []), (1, [(0, u64Layout)])] 1 = some [(0, u64Layout)] from rfl]
  dsimp only [decodeFieldList, Nat.add_zero]
  rw [decodeFromAlloc_int64_scalar env 0 v hLt]
  rfl

/-! ### Golden Case 5.5: Promoted `&U64Range { min: 0, max: 1 }` and `assert_eq!` Promoted Pair -/

def promotedU64RangeTargetAlloc : Allocation :=
  u64RangeSymbolicAlloc 0 1

def promotedU64RangeEnv : AllocEnv :=
  singleAllocEnv 10 promotedU64RangeTargetAlloc

def promotedU64RangeCV : ConstValue :=
  .scalar (.ptr { allocId := 10, offset := 0 } 8)

theorem promotedU64RangeRef_decode_eq :
    decodeConstValue promotedU64RangeEnv 4 promotedU64RangeCV (.ref u64RangeLayout) =
      .ok (.ref (u64RangePure 0 1)) := by
  rfl

def assertionFailedBytes : List Byte :=
  [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 102, 97, 105, 108, 101, 100]

def assertionFailedPureElems : List PureConst :=
  assertionFailedBytes.map (fun b => .int 8 false b.toNat)

def assertEqZeroU32Alloc : Allocation :=
  { bytes := writeLeBytes 0 4
    initMask := List.replicate 4 true
    provenance := []
    align := 4 }

def assertEqStrAlloc : Allocation :=
  { bytes := assertionFailedBytes
    initMask := List.replicate 16 true
    provenance := []
    align := 1 }

def assertEqTupleAlloc : Allocation :=
  { bytes := List.replicate 8 0 ++ List.replicate 8 0 ++ writeLeBytes 16 8
    initMask := List.replicate 24 true
    provenance := [(0, { allocId := 20, offset := 0 }), (8, { allocId := 21, offset := 0 })]
    align := 8 }

def assertEqPromotedEnv : AllocEnv
  | 20 => some (.memory assertEqZeroU32Alloc)
  | 21 => some (.memory assertEqStrAlloc)
  | 22 => some (.memory assertEqTupleAlloc)
  | _ => none

def assertEqPairLayout : TyLayout :=
  .tuple [(0, .ref u32Layout), (8, .sliceRef u8Layout 1)] 24

theorem assertEqSlice_decode_eq :
    decodeConstValue assertEqPromotedEnv 3 (.slice 21 16) (.sliceRef u8Layout 1) =
      .ok (.slice assertionFailedPureElems) := by
  rfl

theorem assertEqPromotedPair_decode_eq :
    decodeConstValue assertEqPromotedEnv 5
      (.scalar (.ptr { allocId := 22, offset := 0 } 8))
      (.ref assertEqPairLayout) =
      .ok (.ref (.tuple [.ref (.int 32 false 0), .slice assertionFailedPureElems])) := by
  rfl

/-! ## Section 5: Small-Step Promoted MIR Body Execution vs. Eager CTFE Equivalence (Theorem 6) -/

/-- Statements in a promoted MIR body `promoted[p]` (which allocates a temporary local, assigns
scalar or aggregate fields, and returns a shared reference `&_temp`). -/
inductive PromotedStmt where
  /-- `StorageLive(localId)`: allocate a fresh temporary memory block of `layout.byteSize` bytes. -/
  | storageLive (localId : Nat) (allocId : AllocId) (layout : TyLayout)
  /-- `(_local + relOffset) = const val`: write a scalar integer field into `localId`'s allocation. -/
  | assignScalarField (localId : Nat) (relOffset : Nat) (bits : Nat) (val : Nat)
  /-- `(_local + relOffset) = Aggregate(c)`: write an encoded constant into `localId`'s allocation. -/
  | assignAggregate (localId : Nat) (relOffset : Nat) (fuel : Nat) (layout : TyLayout) (c : PureConst)
  /-- `_0 = &_local`: intern `localId`'s allocation in `env` and return `&_local`. -/
  | assignRefReturn (srcLocal : Nat)

/-- Small-step runtime state of executing a promoted MIR body `promoted[p]`. -/
structure PromotedExecState where
  locals : Nat → Option (AllocId × Allocation)
  env : AllocEnv
  retVal : Option ConstValue

/-- Initial empty execution state for a promoted MIR body. -/
def initPromotedExecState : PromotedExecState :=
  { locals := fun _ => none
    env := fun _ => none
    retVal := none }

/-- Execute one `PromotedStmt` step. -/
def stepPromotedStmt (st : PromotedExecState) : PromotedStmt → Option PromotedExecState
  | .storageLive localId allocId layout =>
    let alloc := emptyUninitAlloc layout.byteSize 8
    some { st with
      locals := fun l => if l == localId then some (allocId, alloc) else st.locals l }
  | .assignScalarField localId relOffset bits val => do
    let (allocId, alloc) ← st.locals localId
    let alloc' := writeAllocBytes alloc relOffset (writeLeBytes val (bits / 8))
    some { st with
      locals := fun l => if l == localId then some (allocId, alloc') else st.locals l }
  | .assignAggregate localId relOffset fuel layout c => do
    let (allocId, alloc) ← st.locals localId
    let alloc' ← (encodeToAllocAt fuel alloc relOffset layout c).map stripProvenance
    some { st with
      locals := fun l => if l == localId then some (allocId, alloc') else st.locals l }
  | .assignRefReturn srcLocal => do
    let (allocId, alloc) ← st.locals srcLocal
    some { st with
      env := singleAllocEnv allocId alloc
      retVal := some (.scalar (.ptr { allocId := allocId, offset := 0 } 8)) }

/-- Execute a list of promoted MIR statements to completion. -/
def execPromotedStmts (st : PromotedExecState) : List PromotedStmt → Option PromotedExecState
  | [] => some st
  | stmt :: rest => do
    let st' ← stepPromotedStmt st stmt
    execPromotedStmts st' rest

/-- Canonical promoted MIR body that allocates `_1 : targetLayout` at `rtAllocId`, constructs `c`
in `_1`, and assigns `_0 = &_1`. -/
def canonicalPromotedBody (rtAllocId : AllocId) (encFuel : Nat) (targetLayout : TyLayout)
    (c : PureConst) : List PromotedStmt :=
  [ .storageLive 1 rtAllocId targetLayout
  , .assignAggregate 1 0 encFuel targetLayout c
  , .assignRefReturn 1 ]

/-- Execute a promoted MIR body at runtime and decode its returned reference `&_1`. -/
def runAndDecodePromotedBody (decFuel : Nat) (targetLayout : TyLayout)
    (stmts : List PromotedStmt) : Option (Except DecodeError PureConst) := do
  let st ← execPromotedStmts initPromotedExecState stmts
  let retCV ← st.retVal
  some (decodeConstValue st.env decFuel retCV (.ref targetLayout))

/-- Eagerly evaluate `Cid { instance, promoted: Some(p) }` at CTFE (interning the promoted
pointee at `ctfeAllocId`) and decode the resulting `ConstValue.scalar (.ptr ...)`. -/
def evalAndDecodeCtfePromoted (encFuel decFuel : Nat) (ctfeAllocId : AllocId)
    (targetLayout : TyLayout) (c : PureConst) : Option (Except DecodeError PureConst) := do
  let alloc ← encodePureConstToAlloc encFuel targetLayout c
  let ctfeEnv := singleAllocEnv ctfeAllocId alloc
  let ctfeCV : ConstValue := .scalar (.ptr { allocId := ctfeAllocId, offset := 0 } 8)
  some (decodeConstValue ctfeEnv decFuel ctfeCV (.ref targetLayout))

/-- **Theorem 6a (Symbolic Promoted MIR Body Execution vs. Eager CTFE `ConstValue` Equivalence)**:
For ANY `targetLayout : TyLayout`, ANY `c : PureConst`, ANY runtime temporary allocation ID
`rtAllocId : AllocId`, and ANY CTFE interned allocation ID `ctfeAllocId : AllocId`, executing
`canonicalPromotedBody rtAllocId encFuel targetLayout c` at runtime and decoding its return value
produces the **exact same** `PureConst` result as eagerly evaluating `Cid { instance, promoted: Some(p) }`
at CTFE (at `ctfeAllocId`) and decoding its `ConstValue`! -/
theorem promoted_body_exec_eq_ctfe_decode
    (rtAllocId ctfeAllocId : AllocId) (encFuel decFuel : Nat)
    (targetLayout : TyLayout) (c : PureConst) :
    runAndDecodePromotedBody decFuel targetLayout
      (canonicalPromotedBody rtAllocId encFuel targetLayout c) =
      evalAndDecodeCtfePromoted encFuel decFuel ctfeAllocId targetLayout c := by
  have hSelfAlloc : (rtAllocId == rtAllocId) = true := beq_self_eq_true rtAllocId
  have hSelfCtfe : (ctfeAllocId == ctfeAllocId) = true := beq_self_eq_true ctfeAllocId
  simp only [runAndDecodePromotedBody, canonicalPromotedBody, evalAndDecodeCtfePromoted,
    execPromotedStmts, stepPromotedStmt, initPromotedExecState, encodePureConstToAlloc,
    bind, Option.bind, Option.map, beq_self_eq_true, ↓reduceIte]
  cases hEnc : encodeToAllocAt encFuel (emptyUninitAlloc targetLayout.byteSize 8) 0 targetLayout c with
  | none => rfl
  | some alloc =>
    simp only [beq_self_eq_true, ↓reduceIte, decodeConstValue, bne_self_eq_false,
      Bool.false_eq_true, decodeAllocAt, lookupMemoryAlloc, singleAllocEnv, bind, Except.bind]
    rw [decodeFromAlloc_env_irrel_of_no_provenance
      (singleAllocEnv rtAllocId (stripProvenance alloc))
      (singleAllocEnv ctfeAllocId (stripProvenance alloc))
      decFuel (stripProvenance alloc) rfl 0 targetLayout]

/-- Concrete field-by-field promoted MIR body for `&U64Range { min: minVal, max: maxVal }`:
allocates `_1`, writes `_1.min = minVal` at offset `0`, writes `_1.max = maxVal` at offset `8`,
and returns `_0 = &_1`. -/
def promotedU64RangeFieldByFieldBody (rtAllocId : AllocId) (minVal maxVal : Nat) :
    List PromotedStmt :=
  [ .storageLive 1 rtAllocId u64RangeLayout
  , .assignScalarField 1 0 64 minVal
  , .assignScalarField 1 8 64 maxVal
  , .assignRefReturn 1 ]

/-- **Theorem 6b (Field-by-Field Promoted `&U64Range { min: 0, max: 1 }` Execution vs. CTFE)**:
Executing the 4-statement field-by-field promoted MIR body at runtime (`rtAllocId = 999`) and
decoding its return value produces the exact same `.ok (.ref (u64RangePure 0 1))` as decoding
the CTFE `ConstValue` (`ctfeAllocId = 10`). -/
theorem promotedU64Range_fieldByField_exec_eq_ctfe :
    runAndDecodePromotedBody 4 u64RangeLayout (promotedU64RangeFieldByFieldBody 999 0 1) =
      some (decodeConstValue promotedU64RangeEnv 4 promotedU64RangeCV (.ref u64RangeLayout)) ∧
    runAndDecodePromotedBody 4 u64RangeLayout (promotedU64RangeFieldByFieldBody 999 0 1) =
      some (.ok (.ref (u64RangePure 0 1))) := by
  exact ⟨rfl, rfl⟩

theorem writeAllocBytes_u64Range_eq (minVal maxVal : Nat) :
    writeAllocBytes
      (writeAllocBytes (emptyUninitAlloc 16 8) 0 (writeLeBytes minVal 8))
      8 (writeLeBytes maxVal 8) =
      u64RangeSymbolicAlloc minVal maxVal := rfl

/-- **Theorem 6c (Symbolic Field-by-Field Promoted `&U64Range { min, max }` Execution vs. CTFE)**:
For ANY `rtAllocId ctfeAllocId : AllocId` and ANY `minVal, maxVal < 256 ^ 8`, executing the
4-statement field-by-field promoted MIR body (`StorageLive(_1)`, `_1.0 = minVal`, `_1.1 = maxVal`,
`_0 = &_1`) at runtime and decoding its return value produces `.ok (.ref (u64RangePure minVal maxVal))`,
matching eager CTFE evaluation at `ctfeAllocId`. -/
theorem promotedU64Range_fieldByField_symbolic_eq_ctfe
    (rtAllocId ctfeAllocId : AllocId) (minVal maxVal : Nat)
    (hMin : minVal < 256 ^ 8) (hMax : maxVal < 256 ^ 8) :
    runAndDecodePromotedBody 2 u64RangeLayout
      (promotedU64RangeFieldByFieldBody rtAllocId minVal maxVal) =
      some (.ok (.ref (u64RangePure minVal maxVal))) ∧
    decodeConstValue
      (singleAllocEnv ctfeAllocId (u64RangeSymbolicAlloc minVal maxVal))
      2 (.scalar (.ptr { allocId := ctfeAllocId, offset := 0 } 8)) (.ref u64RangeLayout) =
      .ok (.ref (u64RangePure minVal maxVal)) := by
  have hRtEnv :
      singleAllocEnv rtAllocId (u64RangeSymbolicAlloc minVal maxVal) rtAllocId =
        some (GlobalAlloc.memory (u64RangeSymbolicAlloc minVal maxVal)) := by
    dsimp only [singleAllocEnv]
    rw [beq_self_eq_true]
    rfl
  have hCtfeEnv :
      singleAllocEnv ctfeAllocId (u64RangeSymbolicAlloc minVal maxVal) ctfeAllocId =
        some (GlobalAlloc.memory (u64RangeSymbolicAlloc minVal maxVal)) := by
    dsimp only [singleAllocEnv]
    rw [beq_self_eq_true]
    rfl
  have hRtDecode :=
    u64Range_symbolic_roundtrip (singleAllocEnv rtAllocId (u64RangeSymbolicAlloc minVal maxVal))
      rtAllocId minVal maxVal hRtEnv hMin hMax
  have hCtfeDecode :=
    u64Range_symbolic_roundtrip (singleAllocEnv ctfeAllocId (u64RangeSymbolicAlloc minVal maxVal))
      ctfeAllocId minVal maxVal hCtfeEnv hMin hMax
  dsimp only [decodeConstValue] at hRtDecode hCtfeDecode
  constructor
  · simp only [runAndDecodePromotedBody, promotedU64RangeFieldByFieldBody,
      execPromotedStmts, stepPromotedStmt, initPromotedExecState,
      bind, Option.bind, show u64RangeLayout.byteSize = 16 from rfl, Nat.reduceDiv,
      beq_self_eq_true, ↓reduceIte]
    rw [writeAllocBytes_u64Range_eq]
    dsimp only [decodeConstValue, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hRtDecode]
    rfl
  · dsimp only [decodeConstValue, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hCtfeDecode]
    rfl


/-! ## Section 6: Kernel Axiom Audit (`#print axioms`) -/

#print axioms decodeAllocAt_struct_padding_invariant
#print axioms decodeConstValue_remap_invariant
#print axioms decodeAllocAt_int_rejects_provenance
#print axioms decodeAllocAt_bool_rejects_provenance
#print axioms decodeAllocAt_enum_tag_rejects_provenance
#print axioms decodeAllocAt_int_rejects_uninit
#print axioms decodeAllocAt_bool_rejects_uninit
#print axioms decodeAllocAt_niche_tag_rejects_uninit
#print axioms decodeAllocAt_ref_rejects_uninit
#print axioms decodeConstValue_scalar_int_roundtrip
#print axioms decodeConstValue_scalar_bool_roundtrip
#print axioms u64RangeMax_encode_decode_roundtrip
#print axioms u64Range_symbolic_roundtrip
#print axioms u64ScalarValueDataUninit_encode_decode_roundtrip
#print axioms paddedU8U32_initMask_has_uninit_gaps
#print axioms paddedU8U32_encode_decode_roundtrip
#print axioms paddedU8U32_symbolic_roundtrip
#print axioms paddedU8U32_uninit_vs_0xAA_eq
#print axioms encodeDecodeRoundtrip_unit
#print axioms encodeDecodeRoundtrip_bool
#print axioms optionBool_all_roundtrip
#print axioms resultBoolUnit_all_roundtrip
#print axioms optionBool_invalid_byte_3_rejected
#print axioms optionNonZeroU64_none_roundtrip
#print axioms optionNonZeroU64_some_42_roundtrip
#print axioms optionNonZeroU64_some_symbolic_roundtrip
#print axioms promotedU64RangeRef_decode_eq
#print axioms assertEqSlice_decode_eq
#print axioms assertEqPromotedPair_decode_eq
#print axioms promoted_body_exec_eq_ctfe_decode
#print axioms promotedU64Range_fieldByField_exec_eq_ctfe
#print axioms promotedU64Range_fieldByField_symbolic_eq_ctfe

end MirConstAllocationDecoder
