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
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Data.UInt.BasicAux
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.PureLift.MirBridge
public import Anneal.PureLift.SpatialMem.MirMemMirror
public import Anneal.PureLift.SpatialMem.PaddedPin

public section

namespace Anneal.PureLift

open Trusted.MirAst Trusted.MirSemantics

/-!
# `MemoryState` Spatial-Pinning Soundness and Negative Guards (`Soundness`)

Proves universal cross-allocation `MemoryState` framing and end-to-end
`freezePaddedToMem` / `mutatePaddedInMem` / `reabsorbPaddedFromMem` /
`endPaddedLoan` / `deallocatePromotedLocal` soundness
(`paddedStruct_mem_freeze_mutate_reabsorb_sound`) under `BodySpatialCtx`
captured-MIR and per-body `#[repr(C)]` ADT side-table authentication alongside
fail-closed rejection and synchronization tests covering
`LawfulTypedSpatialMemCodec` enforcement (`Trusted.MirSemantics.encodeVal` and
`decodeVal` agreement), `BodySpatialCtx` spoofing rejection, `SpatialTargetSpec`
admission (rejecting `.ref`, general `MirTy.tuple`, and `.unsupported`
pointees), non-padding `.uninit` overwrites, padding non-uniqueness and in-place
reuse validation, codec-independent per-field bidirectional pointer and byte
provenance enforcement (`valAndBytesMatchTargetSpec`), pre-existing
`nextAllocId` reservoir and opaque-decoder collisions (`freshPromotedAllocId`),
`.immediate`, `.immediate none`, `.dead`, and `.indirect` symbolic-to-MIR
synchronization (`writePaddedSymPlace`, `endPaddedLoan`, and
`evalPaddedMirOperand`), aliased promoted `AllocId` rejection, `memBlocks` loan
authentication, single-cause guard isolation, and pinned pure-mutation blocking.
-/

/-! ### `MemoryState` Allocation and Cross-Allocation Framing -/

/-- True iff every allocation ID in `allocs` is strictly below `bound`. -/
@[expose] def memAllocIdsLt (allocs : List Allocation) (bound : AllocId) : Bool
    :=
  allocs.foldr (fun a acc => Nat.blt a.allocId bound && acc) true

/-- True iff every initialized provenance ID in `bs` is below `bound`. -/
@[expose] def bytesProvIdsLt (bs : List AllocByte) (bound : AllocId) : Bool :=
  bs.foldr
    (fun b acc =>
      match b with
      | .uninit | .init _ none => acc
      | .init _ (some p) => Nat.blt p bound && acc)
    true

/-- True iff every provenance ID across `allocs` is strictly below `bound`. -/
@[expose] def memProvIdsLt (allocs : List Allocation) (bound : AllocId) : Bool
    :=
  allocs.foldr (fun a acc => bytesProvIdsLt a.bytes bound && acc) true

private theorem natBeq_false_of_ne (a b : Nat) (hNe : a ≠ b) : Nat.beq a b = false := by
  cases h : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (hNe (natEq_of_beq a b h))

private theorem listAppend_nil_left {α : Type} (xs : List α) : [] ++ xs = xs := rfl

private theorem listAppend_cons {α : Type} (x : α) (xs ys : List α) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

private theorem execFindAllocation_cons (id : AllocId) (a : Allocation)
    (rest : List Allocation) :
    execFindAllocation id (a :: rest) =
      if Nat.beq a.allocId id then some a else execFindAllocation id rest := rfl

private theorem execFindAllocation_none_of_lt (allocs : List Allocation) (id : AllocId)
    (hLt : memAllocIdsLt allocs id = true) :
    execFindAllocation id allocs = none := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [memAllocIdsLt, List.foldr] at hLt
    cases hBlt : Nat.blt a.allocId id with
    | false => rw [hBlt] at hLt; exact False.elim (boolFalseNeTrue hLt)
    | true =>
      rw [hBlt, Bool.true_and] at hLt
      have hNe : a.allocId ≠ id := fun hEq => by
        have hALt := natLt_of_blt a.allocId id hBlt
        rw [hEq] at hALt
        exact Nat.lt_irrefl id hALt
      rw [execFindAllocation_cons, ite_bool_false (natBeq_false_of_ne a.allocId id hNe), ih hLt]

private theorem execFindAllocation_append_lt (allocs : List Allocation) (newAlloc : Allocation)
    (hLt : memAllocIdsLt allocs newAlloc.allocId = true) :
    execFindAllocation newAlloc.allocId (allocs ++ [newAlloc]) = some newAlloc := by
  induction allocs with
  | nil =>
    rw [listAppend_nil_left, execFindAllocation_cons, ite_bool_true (natBeq_refl newAlloc.allocId)]
  | cons a rest ih =>
    dsimp only [memAllocIdsLt, List.foldr] at hLt
    cases hBlt : Nat.blt a.allocId newAlloc.allocId with
    | false => rw [hBlt] at hLt; exact False.elim (boolFalseNeTrue hLt)
    | true =>
      rw [hBlt, Bool.true_and] at hLt
      have hNe : a.allocId ≠ newAlloc.allocId := fun hEq => by
        have hALt := natLt_of_blt a.allocId newAlloc.allocId hBlt
        rw [hEq] at hALt
        exact Nat.lt_irrefl newAlloc.allocId hALt
      have hBeqFalse := natBeq_false_of_ne a.allocId newAlloc.allocId hNe
      rw [listAppend_cons, execFindAllocation_cons, ite_bool_false hBeqFalse, ih hLt]

private theorem execFindAllocation_append_ne (allocs : List Allocation) (newAlloc : Allocation)
    (id : AllocId) (hNe : id ≠ newAlloc.allocId) :
    execFindAllocation id (allocs ++ [newAlloc]) = execFindAllocation id allocs := by
  induction allocs with
  | nil =>
    have hBeqFalse := natBeq_false_of_ne newAlloc.allocId id (fun hEq => hNe hEq.symm)
    rw [listAppend_nil_left, execFindAllocation_cons, ite_bool_false hBeqFalse]
  | cons a rest ih =>
    rw [listAppend_cons, execFindAllocation_cons, execFindAllocation_cons, ih]

private theorem execReplaceAllocation_cons_false (a' a : Allocation) (rest : List Allocation)
    (hFalse : Nat.beq a.allocId a'.allocId = false) :
    execReplaceAllocation a' (a :: rest) = a :: execReplaceAllocation a' rest := by
  dsimp only [execReplaceAllocation, List.foldr]
  rw [ite_bool_false hFalse]

private theorem execReplaceAllocation_append_lt (allocs : List Allocation)
    (oldNew newNew : Allocation)
    (hLt : memAllocIdsLt allocs oldNew.allocId = true)
    (hSameId : newNew.allocId = oldNew.allocId) :
    execReplaceAllocation newNew (allocs ++ [oldNew]) = allocs ++ [newNew] := by
  induction allocs with
  | nil =>
    rw [listAppend_nil_left]
    dsimp only [execReplaceAllocation, List.foldr]
    rw [hSameId, ite_bool_true (natBeq_refl oldNew.allocId)]
    rfl
  | cons a rest ih =>
    dsimp only [memAllocIdsLt, List.foldr] at hLt
    cases hBlt : Nat.blt a.allocId oldNew.allocId with
    | false => rw [hBlt] at hLt; exact False.elim (boolFalseNeTrue hLt)
    | true =>
      rw [hBlt, Bool.true_and] at hLt
      have hNe : a.allocId ≠ newNew.allocId := fun hEq => by
        have hALt := natLt_of_blt a.allocId oldNew.allocId hBlt
        rw [hSameId] at hEq
        rw [hEq] at hALt
        exact Nat.lt_irrefl oldNew.allocId hALt
      have hBeqFalse := natBeq_false_of_ne a.allocId newNew.allocId hNe
      rw [listAppend_cons, execReplaceAllocation_cons_false newNew a (rest ++ [oldNew]) hBeqFalse,
        ih hLt]
      rfl

private theorem bytesFreeOfAllocId_of_provLt (bs : List AllocByte) (aid : AllocId)
    (hLt : bytesProvIdsLt bs aid = true) :
    bytesFreeOfAllocId aid bs = true := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | uninit =>
      dsimp only [bytesProvIdsLt, List.foldr] at hLt
      dsimp only [bytesFreeOfAllocId, List.foldr]
      exact ih hLt
    | init v prov =>
      cases prov with
      | none =>
        dsimp only [bytesProvIdsLt, List.foldr] at hLt
        dsimp only [bytesFreeOfAllocId, List.foldr]
        exact ih hLt
      | some p =>
        dsimp only [bytesProvIdsLt, List.foldr] at hLt
        cases hBlt : Nat.blt p aid with
        | false => rw [hBlt] at hLt; exact False.elim (boolFalseNeTrue hLt)
        | true =>
          rw [hBlt, Bool.true_and] at hLt
          have hNe : p ≠ aid := fun hEq => by
            have hPLt := natLt_of_blt p aid hBlt
            rw [hEq] at hPLt
            exact Nat.lt_irrefl aid hPLt
          change (!Nat.beq p aid && bytesFreeOfAllocId aid rest) = true
          rw [natBeq_false_of_ne p aid hNe, ih hLt]
          rfl

private theorem otherLiveAllocRefsAlloc_append_self (allocs : List Allocation)
    (selfAlloc : Allocation)
    (hProvLt : memProvIdsLt allocs selfAlloc.allocId = true) :
    otherLiveAllocRefsAlloc selfAlloc.allocId (allocs ++ [selfAlloc]) = false := by
  induction allocs with
  | nil =>
    rw [listAppend_nil_left]
    dsimp only [otherLiveAllocRefsAlloc, List.foldr]
    rw [natBeq_refl selfAlloc.allocId]
    rfl
  | cons a rest ih =>
    dsimp only [memProvIdsLt, List.foldr] at hProvLt
    cases hBP : bytesProvIdsLt a.bytes selfAlloc.allocId with
    | false => rw [hBP] at hProvLt; exact False.elim (boolFalseNeTrue hProvLt)
    | true =>
      rw [hBP, Bool.true_and] at hProvLt
      rw [listAppend_cons]
      dsimp only [otherLiveAllocRefsAlloc, List.foldr]
      cases (Nat.beq a.allocId selfAlloc.allocId || !a.live) with
      | true =>
        rw [ite_bool_true rfl]
        exact ih hProvLt
      | false =>
        rw [ite_bool_false rfl, bytesFreeOfAllocId_of_provLt a.bytes selfAlloc.allocId hBP]
        exact ih hProvLt

private theorem otherLiveAllocRefsAlloc_false_of_provLt (allocs : List Allocation)
    (aid : AllocId) (hProvLt : memProvIdsLt allocs aid = true) :
    otherLiveAllocRefsAlloc aid allocs = false := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [memProvIdsLt, List.foldr] at hProvLt
    cases hBP : bytesProvIdsLt a.bytes aid with
    | false => rw [hBP] at hProvLt; exact False.elim (boolFalseNeTrue hProvLt)
    | true =>
      rw [hBP, Bool.true_and] at hProvLt
      dsimp only [otherLiveAllocRefsAlloc, List.foldr]
      cases (Nat.beq a.allocId aid || !a.live) with
      | true =>
        rw [ite_bool_true rfl]
        exact ih hProvLt
      | false =>
        rw [ite_bool_false rfl, bytesFreeOfAllocId_of_provLt a.bytes aid hBP]
        exact ih hProvLt

private theorem anyAllocBytesRefAlloc_false_of_provLt (allocs : List Allocation)
    (aid : AllocId) (hProvLt : memProvIdsLt allocs aid = true) :
    anyAllocBytesRefAlloc aid allocs = false := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [memProvIdsLt, List.foldr] at hProvLt
    cases hBP : bytesProvIdsLt a.bytes aid with
    | false => rw [hBP] at hProvLt; exact False.elim (boolFalseNeTrue hProvLt)
    | true =>
      rw [hBP, Bool.true_and] at hProvLt
      dsimp only [anyAllocBytesRefAlloc, List.foldr]
      rw [bytesFreeOfAllocId_of_provLt a.bytes aid hBP]
      exact ih hProvLt

/-! ### End-to-End Padded `MemoryState` Spatial-Pinning Soundness -/

private theorem execDecodeUInt_singleton (endian : TargetEndian) (b : UInt8) :
    execDecodeUInt endian [b] = b.toNat := by
  cases endian with
  | little | big =>
    dsimp only [execDecodeUInt, execNatOfLeBytes, List.reverse, List.reverseAux, List.foldr]
    have hZ : 256 * 0 = 0 := rfl
    rw [hZ]
    rfl

private theorem u32Bytes_dec_inj (bInit : Nat) (hB : Nat.blt bInit 4294967296 = true) :
    execDecodeUInt execProfileTargetEndian (execEncodeUInt execProfileTargetEndian 4 bInit) = bInit := by
  have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
  have hLt : bInit < Nat.pow 256 4 := by
    rw [hPow4]
    exact natLt_of_blt bInit 4294967296 hB
  exact decodeUInt_encodeUInt_of_lt execProfileTargetEndian 4 bInit hLt

private theorem mirEvalConstLit_uint_i8_eq (a : Nat) (hALt : a < 256) :
    mirEvalConstLit (.int .i8 false) (.scalar (BitVec.ofNat 128 a)) =
      .ok (.scalar ⟨.i8, false, BitVec.ofNat 128 a⟩) := by
  have hPow128 : 256 ≤ Nat.pow 2 128 := natLe_of_ble 256 (Nat.pow 2 128) rfl
  have hPow8 : (256 : Nat) = Nat.pow 2 8 := rfl
  have hBv128 : (BitVec.ofNat 128 a).toNat = a :=
    bitVec128_ofNat_toNat_lt a 256 hALt hPow128
  have hShift0 : Nat.shiftRight a 0 = a := rfl
  have hMod8 : (BitVec.ofNat 8 (Nat.shiftRight a 0)).toNat = a := by
    rw [hShift0]
    change Nat.mod a (Nat.pow 2 8) = a
    rw [← hPow8]
    exact natMod_eq_of_lt hALt
  have hTr :
      mirTruncateBits .i8 (BitVec.ofNat 128 a) = BitVec.ofNat 128 a := by
    dsimp only [mirTruncateBits, mirBitWidth]
    rw [hBv128, hMod8]
  have hNe :
      (mirTruncateBits .i8 (BitVec.ofNat 128 a) != BitVec.ofNat 128 a) = false := by
    rw [hTr]
    dsimp only [bne, BEq.beq]
    rw [decide_eq_true (rfl : BitVec.ofNat 128 a = BitVec.ofNat 128 a)]
    rfl
  dsimp only [mirEvalConstLit]
  rw [ite_bool_false hNe, hTr]

private theorem mirEvalConstLit_uint_i32_eq (b : Nat) (hBLt : b < 4294967296) :
    mirEvalConstLit (.int .i32 false) (.scalar (BitVec.ofNat 128 b)) =
      .ok (.scalar ⟨.i32, false, BitVec.ofNat 128 b⟩) := by
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 := natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hPow32 : (4294967296 : Nat) = Nat.pow 2 32 := rfl
  have hBv128 : (BitVec.ofNat 128 b).toNat = b :=
    bitVec128_ofNat_toNat_lt b 4294967296 hBLt hPow128
  have hShift0 : Nat.shiftRight b 0 = b := rfl
  have hMod32 : (BitVec.ofNat 32 (Nat.shiftRight b 0)).toNat = b := by
    rw [hShift0]
    change Nat.mod b (Nat.pow 2 32) = b
    rw [← hPow32]
    exact natMod_eq_of_lt hBLt
  have hTr :
      mirTruncateBits .i32 (BitVec.ofNat 128 b) = BitVec.ofNat 128 b := by
    dsimp only [mirTruncateBits, mirBitWidth]
    rw [hBv128, hMod32]
  have hNe :
      (mirTruncateBits .i32 (BitVec.ofNat 128 b) != BitVec.ofNat 128 b) = false := by
    rw [hTr]
    dsimp only [bne, BEq.beq]
    rw [decide_eq_true (rfl : BitVec.ofNat 128 b = BitVec.ofNat 128 b)]
    rfl
  dsimp only [mirEvalConstLit]
  rw [ite_bool_false hNe, hTr]

private theorem paddedStruct_loadFieldA (m : MemoryState) (place : MemPlace)
    (aInit bVal : Nat) (hA : Nat.blt aInit 256 = true)
    (hFind : findAllocation place.allocId m.allocations =
      some ⟨place.allocId, 2, .mut,
        [AllocByte.init (UInt8.ofNat aInit) none, .uninit, .uninit, .uninit] ++
        (execEncodeUInt execProfileTargetEndian 4 bVal).map (fun b => AllocByte.init b none),
        true⟩)
    (hOff : place.offset = 0) :
    Trusted.MirSemantics.loadIndirect m (.int .i8 false) ⟨place.allocId, 0⟩ =
      .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 aInit⟩)) := by
  rw [← execFindAllocation_eq] at hFind
  rw [← execLoadIndirect_eq, ← hOff]
  dsimp only [execLoadIndirect, execLayoutOfTy, execIntLayout, execReadBytes]
  rw [hFind]
  dsimp only [execIsInBounds, execIsAligned]
  have hEncLen : (execEncodeUInt execProfileTargetEndian 4 bVal).length = 4 :=
    execEncodeUInt_length execProfileTargetEndian 4 bVal
  cases hXs : execEncodeUInt execProfileTargetEndian 4 bVal with
  | nil => rw [hXs] at hEncLen; nomatch hEncLen
  | cons x0 r1 =>
    cases r1 with
    | nil => rw [hXs] at hEncLen; nomatch hEncLen
    | cons x1 r2 =>
      cases r2 with
      | nil => rw [hXs] at hEncLen; nomatch hEncLen
      | cons x2 r3 =>
        cases r3 with
        | nil => rw [hXs] at hEncLen; nomatch hEncLen
        | cons x3 r4 =>
          cases r4 with
          | cons _ _ => rw [hXs] at hEncLen; nomatch hEncLen
          | nil =>
            dsimp only [List.map, List.append]
            rw [hOff]
            rw [ite_bool_false (rfl : Nat.beq 1 0 = false)]
            rw [ite_bool_false
              (rfl : (!true ||
                !Nat.ble (0 + 1)
                  ([AllocByte.init (UInt8.ofNat aInit) none, .uninit, .uninit, .uninit] ++
                   [AllocByte.init x0 none, .init x1 none, .init x2 none, .init x3 none]).length ||
                !(Nat.ble 0 2 && Nat.beq (Nat.mod 0 (Nat.pow 2 0)) 0)) = false)]
            change
              execDecodeVal execProfileTargetEndian (MirTy.int IntWidth.i8 false)
                [AllocByte.init (UInt8.ofNat aInit) none] =
                .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 aInit⟩))
            dsimp only [execDecodeVal, execDecodeValFallback, execLayoutOfTy, execIntLayout]
            rw [ite_bool_false (rfl : (!Nat.beq ([AllocByte.init (UInt8.ofNat aInit) none]).length 1) = false)]
            rw [ite_bool_false (rfl : Nat.beq 1 0 = false)]
            dsimp only [execInitBytes?, List.foldr]
            have hALt : aInit < 256 := natLt_of_blt aInit 256 hA
            have hU8 : (UInt8.ofNat aInit).toNat = aInit :=
              uint8_toNat_ofNat_lt hALt
            rw [execDecodeUInt_singleton execProfileTargetEndian, hU8, mirEvalConstLit_uint_i8_eq aInit hALt]

private theorem paddedStruct_loadFieldB (m : MemoryState) (place : MemPlace)
    (aInit bVal : Nat) (hB : Nat.blt bVal 4294967296 = true)
    (hFind : findAllocation place.allocId m.allocations =
      some ⟨place.allocId, 2, .mut,
        [AllocByte.init (UInt8.ofNat aInit) none, .uninit, .uninit, .uninit] ++
        (execEncodeUInt execProfileTargetEndian 4 bVal).map (fun b => AllocByte.init b none),
        true⟩) :
    Trusted.MirSemantics.loadIndirect m (.int .i32 false) ⟨place.allocId, 4⟩ =
      .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 bVal⟩)) := by
  rw [← execFindAllocation_eq] at hFind
  rw [← execLoadIndirect_eq]
  dsimp only [execLoadIndirect, execLayoutOfTy, execIntLayout, execReadBytes]
  rw [hFind]
  dsimp only [execIsInBounds, execIsAligned]
  have hEncLen : (execEncodeUInt execProfileTargetEndian 4 bVal).length = 4 :=
    execEncodeUInt_length execProfileTargetEndian 4 bVal
  cases hXs : execEncodeUInt execProfileTargetEndian 4 bVal with
  | nil => rw [hXs] at hEncLen; nomatch hEncLen
  | cons x0 r1 =>
    cases r1 with
    | nil => rw [hXs] at hEncLen; nomatch hEncLen
    | cons x1 r2 =>
      cases r2 with
      | nil => rw [hXs] at hEncLen; nomatch hEncLen
      | cons x2 r3 =>
        cases r3 with
        | nil => rw [hXs] at hEncLen; nomatch hEncLen
        | cons x3 r4 =>
          cases r4 with
          | cons _ _ => rw [hXs] at hEncLen; nomatch hEncLen
          | nil =>
            dsimp only [List.map, List.append]
            rw [ite_bool_false (rfl : Nat.beq 4 0 = false)]
            rw [ite_bool_false
              (rfl : (!true ||
                !Nat.ble (4 + 4)
                  ([AllocByte.init (UInt8.ofNat aInit) none, .uninit, .uninit, .uninit] ++
                   [AllocByte.init x0 none, .init x1 none, .init x2 none, .init x3 none]).length ||
                !(Nat.ble 2 2 && Nat.beq (Nat.mod 4 (Nat.pow 2 2)) 0)) = false)]
            change
              execDecodeVal execProfileTargetEndian (MirTy.int IntWidth.i32 false)
                [AllocByte.init x0 none, .init x1 none, .init x2 none, .init x3 none] =
                .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 bVal⟩))
            dsimp only [execDecodeVal, execDecodeValFallback, execLayoutOfTy, execIntLayout]
            rw [ite_bool_false (rfl : (!Nat.beq ([AllocByte.init x0 none, .init x1 none, .init x2 none, .init x3 none]).length 4) = false)]
            rw [ite_bool_false (rfl : Nat.beq 4 0 = false)]
            dsimp only [execInitBytes?, List.foldr]
            have hDec : execDecodeUInt execProfileTargetEndian [x0, x1, x2, x3] = bVal := by
              rw [← hXs]
              exact u32Bytes_dec_inj bVal hB
            have hBLt : bVal < 4294967296 := natLt_of_blt bVal 4294967296 hB
            rw [hDec, mirEvalConstLit_uint_i32_eq bVal hBLt]

private theorem listTake_of_len_eq {α : Type} {xs : List α} {n : Nat}
    (h : xs.length = n) : xs.take n = xs := by
  have hT := listTake_append_exact xs []
  rw [listAppend_nil_right] at hT
  subst h
  exact hT

private theorem listTake_zero {α : Type} (xs : List α) : xs.take 0 = [] := by
  cases xs with
  | nil | cons _ _ => rfl

private theorem listDrop_replicate_self {α : Type} (n : Nat) (a : α) :
    (List.replicate n a).drop n = [] := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem listLength_replicate {α : Type} (n : Nat) (a : α) :
    (List.replicate n a).length = n := by
  induction n with
  | zero => rfl
  | succ n' ih => exact congrArg Nat.succ ih

private theorem natAdd_zero_l (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBeq_zero_of_pos {n : Nat} (h : 0 < n) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ _ => rfl

/-- Test fixture helper building an authenticated `BodySpatialCtx` whose
captured `Body.locals` and `adtLocals` side-table match `specs` under
`idStr`. -/
@[expose] def mkBodyCtxOfSpecs (idStr : String)
    (specs : List SpatialTargetSpec) : BodySpatialCtx :=
  { body :=
      { argumentCount := 0
        locals := specs.map SpatialTargetSpec.toCapturedMirTy
        basicBlocks := [{ statements := [], terminator := .return_ }]
        isUnsafe := false
        identity := idStr }
    adtLocals :=
      specs.foldr
        (fun s k idx =>
          match s with
          | .mirTy _ => k (idx + 1)
          | .reprCAdt tag fs => ⟨idStr, idx, tag, fs⟩ :: k (idx + 1))
        (fun _ => [])
        0 }

/-- Soundness test fixture `u8U32Ctx1`. -/
@[expose] def u8U32Ctx1 : BodySpatialCtx :=
  mkBodyCtxOfSpecs "u8_u32_1" [paddedU8U32MemCodec.targetTy]

/-- Soundness test fixture `u8U32Ctx2`. -/
@[expose] def u8U32Ctx2 : BodySpatialCtx :=
  mkBodyCtxOfSpecs "u8_u32_2" [.mirTy .unit, paddedU8U32MemCodec.targetTy]

/-- Authenticated `BodySpatialCtx` fixture for `paddedU8U32MemCodec`. -/
@[expose] def sampleBodyCtx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "sample_u8_u32"
    [.mirTy .unit, paddedU8U32MemCodec.targetTy,
     .mirTy (.ref .mut paddedU8U32MemCodec.targetTy.toCapturedMirTy)]

/-- Soundness test fixture `provBodyCtx`. -/
@[expose] def provBodyCtx (expectedProv : AllocId) : BodySpatialCtx :=
  mkBodyCtxOfSpecs "prov_ptr"
    [.mirTy .unit, (provPtrPaddedMemCodec expectedProv).targetTy]

/-- Soundness test fixture `zstBodyCtx`. -/
@[expose] def zstBodyCtx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "zst_2" [.mirTy .unit, .mirTy .unit]

/-- Soundness test fixture `u32SyncCtx`. -/
@[expose] def u32SyncCtx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "u32_sync"
    [.mirTy .unit, .mirTy (.int .i32 false),
     .mirTy (.ref .mut (.int .i32 false))]

/-- Soundness test fixture `immBoolU32Ctx`. -/
@[expose] def immBoolU32Ctx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "imm_bool_u32" [.mirTy .bool, .mirTy (.int .i32 false)]

/-- Soundness test fixture `immBoolRefCtx`. -/
@[expose] def immBoolRefCtx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "imm_bool_ref" [.mirTy .bool, .mirTy (.ref .mut .unit)]

/-- Soundness test fixture `unitU32Ctx`. -/
@[expose] def unitU32Ctx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "unit_u32" [.mirTy .unit, .mirTy (.int .i32 false)]

/-- Soundness test fixture `deallocReg0Ctx`. -/
@[expose] def deallocReg0Ctx : BodySpatialCtx :=
  mkBodyCtxOfSpecs "dealloc_reg0" [u8U32TargetSpec, .mirTy .unit]

/-- Generic unmodified `freezePaddedToMem` / `reabsorbPaddedFromMem` round-trip
soundness over any positive-size `LawfulTypedSpatialMemCodec`
(`0 < c.layout.size`): freezing an accepted value `v` into `MemoryState` and
reabsorbing without mutation restores `.activeMut` on `v` while preserving
disjoint `MemoryState` allocations. -/
theorem lawfulCodec_mem_freeze_reabsorb_roundtrip_sound {α : Type}
    (ctx : BodySpatialCtx)
    (c : TypedSpatialMemCodec α)
    (hCtx : specsMatchBodyCtx ctx [c.targetTy] = true)
    (hLaw : LawfulTypedSpatialMemCodec c)
    (hSizePos : 0 < c.layout.size)
    (hTyRefl : spatialTargetSpecBeq c.targetTy c.targetTy = true)
    (v : Val) (x : α)
    (hDec : c.decodeFromSymVal v = some x)
    (hValRefl : mirValBeqAt 8 v v = true)
    (m0 : MemoryState)
    (hFresh : memAllocIdsLt m0.allocations m0.nextAllocId = true)
    (hProvFresh : memProvIdsLt m0.allocations m0.nextAllocId = true)
    (hValFree : valFreeOfAllocId 8 m0.nextAllocId v = true)
    (hRep :
      replaceableVal mirValAlg
        [⟨0, .spatialPinned 1 (paddedLoanWitnessCodec c 0 ⟨m0.nextAllocId, 0⟩),
          ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩]
        v v = true)
    (otherPlace : MemPlace) (otherSize otherAlign : Nat)
    (hOtherId : otherPlace.allocId ≠ m0.nextAllocId) :
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨v, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [c.targetTy]
        mirLocals := [.immediate (some v)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    let place : MemPlace := ⟨m0.nextAllocId, 0⟩
    Exists fun stPinned =>
    Exists fun stReabsorbed =>
      freezePaddedToMem ctx 0 c hLaw st0 = .ok stPinned ∧
      stPinned.mirLocals = [.indirect place] ∧
      reabsorbPaddedFromMem ctx 0 stPinned = .ok stReabsorbed ∧
      stReabsorbed.mirLocals = [.indirect place] ∧
      findLoan 0 stReabsorbed.sym.loans =
        some ⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩ ∧
      Trusted.MirSemantics.readBytes stPinned.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign ∧
      Trusted.MirSemantics.readBytes stReabsorbed.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign := by
  intro st0 place
  have hMaskLen : c.padMask.length = c.layout.size := hLaw.2.1
  have hRawLen : (c.encodeValToMem x).length = c.layout.size := (hLaw.2.2.1 x).1
  have hNonPad : nonPadBytesInitialized c.padMask (c.encodeValToMem x) = true :=
    (hLaw.2.2.1 x).2.1
  have hProv : c.provCheck (c.encodeValToMem x) = true := (hLaw.2.2.1 x).2.2.1
  have hCompatX : valCompatWithTargetSpec (c.encodeToSymVal x) c.targetTy = true :=
    (hLaw.2.2.1 x).2.2.2.1
  have hBytesMatchTrueX :
      valAndBytesMatchTargetSpec true c.targetTy (c.encodeToSymVal x)
        (c.encodeValToMem x) = true :=
    (hLaw.2.2.1 x).2.2.2.2.1
  have hBytesMatchFalseX :
      valAndBytesMatchTargetSpec false c.targetTy (c.encodeToSymVal x)
        (c.encodeValToMem x) = true :=
    valAndBytesMatchTargetSpec_false_of_true c.targetTy (c.encodeToSymVal x)
      (c.encodeValToMem x) hBytesMatchTrueX
  have hDecMem : c.decodeValFromMem (c.encodeValToMem x) = some x :=
    (hLaw.2.2.1 x).2.2.2.2.2.1
  have hEncSym : c.encodeToSymVal x = v := hLaw.2.2.2.1 v x hDec
  let rawBytes := c.encodeValToMem x
  let allocUninit : Allocation :=
    { allocId := m0.nextAllocId
      alignLog2 := c.layout.alignLog2
      mutability := .mut
      bytes := List.replicate c.layout.size .uninit
      live := true }
  let allocPinned : Allocation :=
    { allocId := m0.nextAllocId
      alignLog2 := c.layout.alignLog2
      mutability := .mut
      bytes := rawBytes
      live := true }
  let memPinned : MemoryState :=
    { nextAllocId := m0.nextAllocId + 1
      allocations := m0.allocations ++ [allocPinned] }
  let witness0 := paddedLoanWitnessCodec c 0 place
  let blkPinned : PaddedSpatialBlock :=
    ⟨1, 0, 0, .readWrite, 1, 0, c.layout, place, c.codecId⟩
  let entryPinned : PromotedLocalEntry :=
    ⟨0, c.targetTy, place, c.layout, c.padMask, c.codecId, encodeSymOfCodec c⟩
  let stPinned : PaddedSymMemState :=
    { sym :=
        { locals := st0.sym.locals
          loans :=
            [⟨0, .spatialPinned 1 witness0, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩]
          regionGroups := []
          regionDeposits := []
          spatial := []
          nextSpatialTag := 2 }
      mirLocalTypes := [c.targetTy]
      mirLocals := [.indirect place]
      mem := memPinned
      memBlocks := [blkPinned]
      promotedLocals := [entryPinned] }
  let stReabsorbed : PaddedSymMemState :=
    { sym :=
        { locals := st0.sym.locals
          loans := [⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩]
          regionGroups := []
          regionDeposits := []
          spatial := []
          nextSpatialTag := 2 }
      mirLocalTypes := [c.targetTy]
      mirLocals := [.indirect place]
      mem := memPinned
      memBlocks := []
      promotedLocals := [entryPinned] }
  have hFindUninit :
      execFindAllocation m0.nextAllocId (m0.allocations ++ [allocUninit]) = some allocUninit :=
    execFindAllocation_append_lt m0.allocations allocUninit hFresh
  have hReplPinned :
      execReplaceAllocation allocPinned (m0.allocations ++ [allocUninit]) =
        m0.allocations ++ [allocPinned] :=
    execReplaceAllocation_append_lt m0.allocations allocUninit allocPinned hFresh rfl
  have hFindPinned :
      execFindAllocation m0.nextAllocId (m0.allocations ++ [allocPinned]) = some allocPinned :=
    execFindAllocation_append_lt m0.allocations allocPinned hFresh
  have hRawZero : Nat.beq rawBytes.length 0 = false := by
    change Nat.beq (c.encodeValToMem x).length 0 = false
    rw [hRawLen]
    exact natBeq_zero_of_pos hSizePos
  have hSzZero : Nat.beq c.layout.size 0 = false := natBeq_zero_of_pos hSizePos
  have hBleSize : Nat.ble c.layout.size c.layout.size = true :=
    natBle_of_le c.layout.size c.layout.size (Nat.le_refl _)
  have hBleAlign : Nat.ble c.layout.alignLog2 c.layout.alignLog2 = true :=
    natBle_of_le c.layout.alignLog2 c.layout.alignLog2 (Nat.le_refl _)
  have hModZero : Nat.beq (Nat.mod 0 (Nat.pow 2 c.layout.alignLog2)) 0 = true := rfl
  have hFreeze : freezePaddedToMem ctx 0 c hLaw st0 = .ok stPinned := by
    have hPureOk :
        (!((@LoanPhase.activeMut Val).isActiveMut &&
           isUnborrowed PermTree.unborrowed &&
           noActiveChildLoanEdgesIn mirValAlg 0 st0.sym.loans &&
           noActiveChildRegionEdges 0 st0.sym.regionGroups &&
           Nat.beq (countPaddedBlocksForLoan 0 st0.memBlocks) 0 &&
           !hasPaddedBlockId st0.sym.nextSpatialTag st0.memBlocks &&
           Nat.beq (countBlocksForLoan 0 st0.sym.spatial) 0 &&
           !hasSpatialBlockId st0.sym.nextSpatialTag st0.sym.spatial)) = false := rfl
    have hTyBad : (!spatialTargetSpecBeq c.targetTy c.targetTy) = false := by
      rw [hTyRefl]
      rfl
    have hCompatV : valCompatWithTargetSpec v c.targetTy = true := by
      rw [← hEncSym]
      exact hCompatX
    have hBytesMatchV :
        valAndBytesMatchTargetSpec true c.targetTy v rawBytes = true := by
      change
        valAndBytesMatchTargetSpec true c.targetTy v (c.encodeValToMem x) = true
      rw [← hEncSym]
      exact hBytesMatchTrueX
    have hEncOk :
        (!(mirValBeqAt 8 (c.encodeToSymVal x) v &&
           valCompatWithTargetSpec v c.targetTy &&
           Nat.beq rawBytes.length c.layout.size &&
           Nat.beq c.padMask.length c.layout.size &&
           nonPadBytesInitialized c.padMask rawBytes &&
           c.provCheck rawBytes &&
           valAndBytesMatchTargetSpec true c.targetTy v rawBytes)) = false := by
      change
        (!(mirValBeqAt 8 (c.encodeToSymVal x) v &&
           valCompatWithTargetSpec v c.targetTy &&
           Nat.beq (c.encodeValToMem x).length c.layout.size &&
           Nat.beq c.padMask.length c.layout.size &&
           nonPadBytesInitialized c.padMask (c.encodeValToMem x) &&
           c.provCheck (c.encodeValToMem x) &&
           valAndBytesMatchTargetSpec true c.targetTy v rawBytes)) = false
      rw [hEncSym, hValRefl, hCompatV, hRawLen, hMaskLen, natBeq_refl c.layout.size,
        hNonPad, hProv, hBytesMatchV]
      rfl
    have hValSlot : (!mirValBeqAt 8 v v) = false := by rw [hValRefl]; rfl
    have hFreshIdOk : (!freshPromotedAllocId 0 m0.nextAllocId st0) = false := by
      dsimp only [freshPromotedAllocId, st0, allocExclusivelyOwnedByLocal,
        anyBlockUsesAlloc, indirectLocalsUseAlloc, anyPromotedEntryUsesAlloc,
        otherPromotedEntryUsesAlloc, otherLocalUsesAlloc, otherSymLocalUsesAlloc,
        activeLoanValUsesAlloc, backTargetUsesAlloc, BackTarget.direct,
        pureSpatialUsesAlloc, regionDepositsUseAlloc, activeRegionGroupExists,
        LoanPhase.isEnded, mirListGet?, List.foldr]
      rw [execFindAllocation_none_of_lt m0.allocations m0.nextAllocId hFresh,
        hValFree,
        otherLiveAllocRefsAlloc_false_of_provLt m0.allocations m0.nextAllocId hProvFresh,
        anyAllocBytesRefAlloc_false_of_provLt m0.allocations m0.nextAllocId hProvFresh]
      rfl
    have hAllocOk :
        (!allocUninit.live || !execIsInBounds allocUninit 0 rawBytes.length ||
          !execIsAligned allocUninit 0 c.layout.alignLog2) = false := by
      dsimp only [allocUninit, execIsInBounds, execIsAligned, rawBytes]
      rw [hRawLen, listLength_replicate, natAdd_zero_l, hBleSize, hBleAlign, hModZero]
      rfl
    have hTakeDrop :
        allocUninit.bytes.take 0 ++ rawBytes ++
          allocUninit.bytes.drop (0 + rawBytes.length) = rawBytes := by
      dsimp only [allocUninit, rawBytes]
      rw [listTake_zero, listAppend_nil_left, natAdd_zero_l, hRawLen,
        listDrop_replicate_self, listAppend_nil_right]
    have hCtx0 : (!specsMatchBodyCtx ctx st0.mirLocalTypes ||
        !Nat.beq st0.mirLocalTypes.length st0.mirLocals.length) = false := by
      dsimp only [st0]; rw [hCtx]; rfl
    dsimp only [freezePaddedToMem]
    rw [ite_bool_false hCtx0]
    rw [ite_bool_false (rfl : (!hasUniqueLoanId 0 st0.sym.loans) = false)]
    have hFindL :
        findLoan 0 st0.sym.loans =
          some ⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩ := rfl
    rw [hFindL]
    dsimp only
    rw [ite_bool_false hPureOk]
    dsimp only [loanDirectLocal?, BackTarget.direct]
    have hGetTy : mirListGet? st0.mirLocalTypes 0 = some c.targetTy := rfl
    rw [hGetTy]
    dsimp only
    rw [ite_bool_false hTyBad]
    rw [ite_bool_false (rfl : (!ownerLocalExclusivelyHeldByLoan 0 0 st0.sym) = false)]
    rw [hDec]
    dsimp only
    rw [ite_bool_false hEncOk]
    dsimp only [st0, mirListGet?, List.foldr]
    rw [ite_bool_false hValSlot,
      ite_bool_false (rfl : hasPromotedLocalEntry 0 [] = false),
      ite_bool_false hFreshIdOk]
    dsimp only [execAllocateStack, execReserveAllocId, execWriteBytes]
    have hUninitEq :
        ({ allocId := m0.nextAllocId, alignLog2 := c.layout.alignLog2, mutability := .mut,
           bytes := List.replicate c.layout.size .uninit, live := true } : Allocation) =
          allocUninit := rfl
    rw [hUninitEq, hFindUninit]
    dsimp only
    rw [ite_bool_false hRawZero, ite_bool_false hAllocOk, hTakeDrop]
    have hPinnedEq :
        ({ allocId := m0.nextAllocId, alignLog2 := c.layout.alignLog2, mutability := .mut,
           bytes := rawBytes, live := true } : Allocation) = allocPinned := rfl
    rw [hPinnedEq, hReplPinned]
    rfl
  have hReabsorb : reabsorbPaddedFromMem ctx 0 stPinned = .ok stReabsorbed := by
    have hSymCoh :
        (!pinnedLoanSymCoherent
            ⟨0, .spatialPinned 1 witness0, ⟨v, .unborrowed⟩,
              ⟨[.direct (.localReg 0) []]⟩⟩
            0 blkPinned [] stPinned.sym) = false := rfl
    have hPinBad :
        (!(Nat.beq blkPinned.originLoan 0 &&
           Nat.beq blkPinned.provenanceTag 1 &&
           witnessMatchesBlock witness0 0 blkPinned &&
           Nat.beq c.layout.size blkPinned.layout.size &&
           Nat.beq c.layout.alignLog2 blkPinned.layout.alignLog2 &&
           (match blkPinned.perm with | .readWrite => true | .readOnly => false) &&
           Nat.beq blkPinned.activeSubSplits 0)) = false := by
      dsimp only [blkPinned, witnessMatchesBlock, witness0, paddedLoanWitnessCodec, place, stPinned]
      rw [natBeq_refl c.codecId, natBeq_refl m0.nextAllocId,
        natBeq_refl c.layout.size, natBeq_refl c.layout.alignLog2]
      rfl
    have hSlotBad :
        (!slotMatchesIndirection stPinned.mirLocals 0 blkPinned.place ||
         otherPromotedEntryUsesAlloc 0 blkPinned.place.allocId
           stPinned.promotedLocals ||
         otherIndirectLocalUsesAlloc 0 blkPinned.place.allocId
           stPinned.mirLocals) = false := by
      dsimp only [slotMatchesIndirection, otherPromotedEntryUsesAlloc,
        otherIndirectLocalUsesAlloc, stPinned, entryPinned, blkPinned,
        place, mirListGet?, List.foldr]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hSliceOk :
        (!liveMutSliceValid stPinned.mem blkPinned.place blkPinned.layout) = false := by
      dsimp only [liveMutSliceValid, stPinned, memPinned, blkPinned, place,
        execIsInBounds, execIsAligned]
      rw [hFindPinned]
      dsimp only [allocPinned, rawBytes]
      rw [hRawLen, natAdd_zero_l, hBleSize, hBleAlign, hModZero]
      rfl
    have hReadPinned :
        execReadBytes stPinned.mem blkPinned.place blkPinned.layout.size
          blkPinned.layout.alignLog2 = .ok rawBytes := by
      have hRdOk :
          (!allocPinned.live || !execIsInBounds allocPinned 0 c.layout.size ||
            !execIsAligned allocPinned 0 c.layout.alignLog2) = false := by
        dsimp only [allocPinned, execIsInBounds, execIsAligned, rawBytes]
        rw [hRawLen, natAdd_zero_l, hBleSize, hBleAlign, hModZero]
        rfl
      dsimp only [execReadBytes, stPinned, memPinned, blkPinned, place]
      rw [hFindPinned]
      dsimp only
      rw [ite_bool_false hSzZero, ite_bool_false hRdOk, listDrop_zero]
      exact congrArg Except.ok (listTake_of_len_eq hRawLen)
    have hWitnessDec :
        witness0.decode [.uninit, .init (.bytes rawBytes)] = some v := by
      dsimp only [witness0, paddedLoanWitnessCodec, rawBytes]
      have hNP : (!nonPadBytesInitialized c.padMask (c.encodeValToMem x)) = false := by
        rw [hNonPad]; rfl
      have hPR : (!c.provCheck (c.encodeValToMem x)) = false := by
        rw [hProv]; rfl
      have hPS :
          (!valAndBytesMatchTargetSpec false c.targetTy
            (c.encodeToSymVal x) (c.encodeValToMem x)) = false := by
        rw [hBytesMatchFalseX]; rfl
      rw [ite_bool_false hNP, ite_bool_false hPR, hDecMem]
      dsimp only
      rw [ite_bool_false hPS, hEncSym]
    have hNonPadFalse : (!nonPadBytesInitialized c.padMask rawBytes) = false := by
      change (!nonPadBytesInitialized c.padMask (c.encodeValToMem x)) = false
      rw [hNonPad]; rfl
    have hCompatVFalse : (!valCompatWithTargetSpec v c.targetTy) = false := by
      rw [← hEncSym, hCompatX]; rfl
    have hMatchVFalse :
        (!valAndBytesMatchTargetSpec false c.targetTy v rawBytes) = false := by
      change (!valAndBytesMatchTargetSpec false c.targetTy v (c.encodeValToMem x)) = false
      rw [← hEncSym, hBytesMatchFalseX]; rfl
    have hRepFalse : (!replaceableVal mirValAlg stPinned.sym.loans v v) = false := by
      dsimp only [stPinned, witness0, place]
      rw [hRep]
      rfl
    have hCtxP : (!specsMatchBodyCtx ctx stPinned.mirLocalTypes ||
        !Nat.beq stPinned.mirLocalTypes.length stPinned.mirLocals.length) = false := by
      dsimp only [stPinned]; rw [hCtx]; rfl
    dsimp only [reabsorbPaddedFromMem]
    rw [ite_bool_false hCtxP]
    rw [ite_bool_false (rfl : (!hasUniqueLoanId 0 stPinned.sym.loans) = false)]
    have hFindL :
        findLoan 0 stPinned.sym.loans =
          some ⟨0, .spatialPinned 1 witness0, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩ := rfl
    rw [hFindL]
    dsimp only [loanDirectLocal?, BackTarget.direct]
    have hFindB : findPaddedSpatialBlock stPinned.memBlocks 1 = some (blkPinned, []) := rfl
    rw [hFindB]
    dsimp only
    rw [ite_bool_false hSymCoh]
    have hGetTy : mirListGet? stPinned.mirLocalTypes 0 = some c.targetTy := rfl
    rw [hGetTy]
    dsimp only
    rw [hLaw.1]
    dsimp only
    rw [ite_bool_false hPinBad, ite_bool_false hSlotBad,
      ite_bool_false hSliceOk, hReadPinned]
    dsimp only
    rw [hWitnessDec]
    dsimp only
    rw [ite_bool_false hNonPadFalse, ite_bool_false hCompatVFalse,
      ite_bool_false hMatchVFalse, ite_bool_false hRepFalse]
    rfl
  have hFramePinned :
      Trusted.MirSemantics.readBytes stPinned.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign := by
    rw [← execReadBytes_eq, ← execReadBytes_eq]
    dsimp only [execReadBytes, stPinned, memPinned]
    rw [execFindAllocation_append_ne m0.allocations allocPinned otherPlace.allocId hOtherId]
  exact ⟨stPinned, stReabsorbed,
    hFreeze, rfl, hReabsorb, rfl, rfl, hFramePinned, hFramePinned⟩

/-- Concrete non-vacuity instantiation of
`lawfulCodec_mem_freeze_reabsorb_roundtrip_sound` at `paddedU8U32MemCodec`,
discharging `hTyRefl`, `hDec`, `hValRefl`, `hFresh`, `hProvFresh`, `hValFree`,
and `hRep` by `rfl`. -/
theorem paddedU8U32_mem_freeze_reabsorb_roundtrip_corollary :
    let v := paddedU8U32MemCodec.encodeToSymVal ⟨0x11, BitVec.ofNat 32 0x22334455⟩
    let m0 : MemoryState := ⟨1, []⟩
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨v, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [paddedU8U32MemCodec.targetTy]
        mirLocals := [.immediate (some v)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    Exists fun stPinned =>
    Exists fun stReabsorbed =>
      freezePaddedToMem u8U32Ctx1 0 paddedU8U32MemCodec
        paddedU8U32MemCodec_lawful st0 = .ok stPinned ∧
      reabsorbPaddedFromMem u8U32Ctx1 0 stPinned = .ok stReabsorbed ∧
      findLoan 0 stReabsorbed.sym.loans =
        some ⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 0) []⟩ := by
  intro v m0 st0
  have hMain :=
    lawfulCodec_mem_freeze_reabsorb_roundtrip_sound
      u8U32Ctx1 paddedU8U32MemCodec rfl paddedU8U32MemCodec_lawful (Nat.zero_lt_succ 7) rfl
      v ⟨0x11, BitVec.ofNat 32 0x22334455⟩ rfl rfl m0 rfl rfl rfl rfl ⟨2, 0⟩ 4 2
      (fun h => nomatch h)
  cases hMain with
  | intro stPinned hRest =>
    cases hRest with
    | intro stReabsorbed hConj =>
      exact ⟨stPinned, stReabsorbed, hConj.1, hConj.2.2.1, hConj.2.2.2.2.1⟩

/-- End-to-end soundness and cross-allocation framing for `paddedU8U32MemCodec`
across `freezePaddedToMem`, `mutatePaddedInMem` (`writeBytes`), field loads
(`loadIndirect`) with `.uninit` padding preserved, `reabsorbPaddedFromMem`,
`endPaddedLoan` (`endLoanInState` + `syncPromotedLocalsToMem`), and
`deallocatePromotedLocal` (`deallocateStack` on non-return local `1`). -/
theorem paddedStruct_mem_freeze_mutate_reabsorb_sound
    (aInit bInit bNew : Nat)
    (hA : Nat.blt aInit 256 = true)
    (hBNew : Nat.blt bNew 4294967296 = true)
    (m0 : MemoryState)
    (hFresh : memAllocIdsLt m0.allocations m0.nextAllocId = true)
    (hProvFresh : memProvIdsLt m0.allocations m0.nextAllocId = true)
    (otherPlace : MemPlace) (otherSize otherAlign : Nat)
    (hOtherId : otherPlace.allocId ≠ m0.nextAllocId) :
    let initStruct : U8U32Struct := ⟨UInt8.ofNat aInit, BitVec.ofNat 32 bInit⟩
    let newStruct : U8U32Struct := ⟨UInt8.ofNat aInit, BitVec.ofNat 32 bNew⟩
    let initSymVal : Val := paddedU8U32MemCodec.encodeToSymVal initStruct
    let newSymVal : Val := paddedU8U32MemCodec.encodeToSymVal newStruct
    let bNewMemBytes : List AllocByte :=
      (execEncodeUInt execProfileTargetEndian 4 bNew).map (fun b => AllocByte.init b none)
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.unit, .unborrowed⟩, ⟨initSymVal, .mutLocked 0⟩]
            loans := [⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
        mirLocals := [.immediate (some .unit), .immediate (some initSymVal)]
        mem := m0
        memBlocks := []
        promotedLocals := [] }
    let place : MemPlace := ⟨m0.nextAllocId, 0⟩
    Exists fun stPinned =>
    Exists fun stMut =>
    Exists fun stReabsorbed =>
    Exists fun stEndSym =>
    Exists fun stDealloc =>
      freezePaddedToMem u8U32Ctx2 0 paddedU8U32MemCodec
        paddedU8U32MemCodec_lawful st0 = .ok stPinned ∧
      stPinned.mirLocals = [.immediate (some .unit), .indirect place] ∧
      mutatePaddedInMem u8U32Ctx2 1 1 4 2 bNewMemBytes stPinned = .ok stMut ∧
      Trusted.MirSemantics.writeBytes stPinned.mem ⟨place.allocId, 4⟩ 2 bNewMemBytes =
        .ok stMut.mem ∧
      Trusted.MirSemantics.readBytes stMut.mem ⟨place.allocId, 1⟩ 3 0 =
        .ok [.uninit, .uninit, .uninit] ∧
      Trusted.MirSemantics.loadIndirect stMut.mem (.int .i8 false) ⟨place.allocId, 0⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 aInit⟩)) ∧
      Trusted.MirSemantics.loadIndirect stMut.mem (.int .i32 false) ⟨place.allocId, 4⟩ =
        .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 bNew⟩)) ∧
      reabsorbPaddedFromMem u8U32Ctx2 0 stMut =
        .ok stReabsorbed ∧
      stReabsorbed.mirLocals = [.immediate (some .unit), .indirect place] ∧
      Trusted.MirSemantics.loadIndirect stReabsorbed.mem (.int .i8 false) ⟨place.allocId, 0⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 aInit⟩)) ∧
      Trusted.MirSemantics.loadIndirect stReabsorbed.mem (.int .i32 false) ⟨place.allocId, 4⟩ =
        .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 bNew⟩)) ∧
      endLoanInState mirValAlg 0 stReabsorbed.sym = .ok stEndSym ∧
      endPaddedLoan u8U32Ctx2 0 stReabsorbed =
        .ok { stReabsorbed with sym := stEndSym } ∧
      getLocal mirValAlg 1 stEndSym = some newSymVal ∧
      deallocatePromotedLocal u8U32Ctx2 1
        { stReabsorbed with sym := stEndSym } = .ok stDealloc ∧
      stDealloc.mirLocals = [.immediate (some .unit), .dead] ∧
      stDealloc.promotedLocals = [] ∧
      getLocal mirValAlg 1 stDealloc.sym = some .unit ∧
      Trusted.MirSemantics.deallocateStack stReabsorbed.mem place = .ok stDealloc.mem ∧
      Trusted.MirSemantics.readBytes stPinned.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign ∧
      Trusted.MirSemantics.readBytes stMut.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign ∧
      Trusted.MirSemantics.readBytes stReabsorbed.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign ∧
      Trusted.MirSemantics.readBytes stDealloc.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign := by
  intro initStruct newStruct initSymVal newSymVal bNewMemBytes st0 place
  have hLawful := paddedU8U32MemCodec_lawful
  have hDecSymInit : paddedU8U32MemCodec.decodeFromSymVal initSymVal = some initStruct :=
    (hLawful.2.2.1 initStruct).2.2.2.2.2.2
  have hInitRawLen : (paddedU8U32Encode initStruct).length = 8 :=
    (hLawful.2.2.1 initStruct).1
  have hInitNonPad :
      nonPadBytesInitialized u8PadU32Mask (paddedU8U32Encode initStruct) = true :=
    (hLawful.2.2.1 initStruct).2.1
  have hInitCompat :
      valCompatWithTargetSpec initSymVal paddedU8U32MemCodec.targetTy = true :=
    (hLawful.2.2.1 initStruct).2.2.2.1
  have hInitBytesMatch :
      valAndBytesMatchTargetSpec true paddedU8U32MemCodec.targetTy initSymVal
        (paddedU8U32Encode initStruct) = true :=
    (hLawful.2.2.1 initStruct).2.2.2.2.1
  let allocUninit : Allocation :=
    { allocId := m0.nextAllocId
      alignLog2 := 2
      mutability := .mut
      bytes := List.replicate 8 .uninit
      live := true }
  let initRawBytes := paddedU8U32Encode initStruct
  let allocPinned : Allocation :=
    { allocId := m0.nextAllocId
      alignLog2 := 2
      mutability := .mut
      bytes := initRawBytes
      live := true }
  let memPinned : MemoryState :=
    { nextAllocId := m0.nextAllocId + 1
      allocations := m0.allocations ++ [allocPinned] }
  let witness0 := paddedLoanWitnessCodec paddedU8U32MemCodec 1 place
  let blkPinned : PaddedSpatialBlock :=
    ⟨1, 0, 1, .readWrite, 1, 0, ⟨8, 2⟩, place, 8032⟩
  let entryPinned : PromotedLocalEntry :=
    ⟨1, paddedU8U32MemCodec.targetTy, place, ⟨8, 2⟩, u8PadU32Mask, 8032,
     encodeSymOfCodec paddedU8U32MemCodec⟩
  let stPinned : PaddedSymMemState :=
    { sym :=
        { locals := st0.sym.locals
          loans :=
            [⟨0, .spatialPinned 1 witness0,
              ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
          regionGroups := []
          regionDeposits := []
          spatial := []
          nextSpatialTag := 2 }
      mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
      mirLocals := [.immediate (some .unit), .indirect place]
      mem := memPinned
      memBlocks := [blkPinned]
      promotedLocals := [entryPinned] }
  let mutRawBytes :=
    [AllocByte.init (UInt8.ofNat aInit) none, .uninit, .uninit, .uninit] ++ bNewMemBytes
  let allocMut : Allocation :=
    { allocId := m0.nextAllocId
      alignLog2 := 2
      mutability := .mut
      bytes := mutRawBytes
      live := true }
  let memMut : MemoryState :=
    { nextAllocId := m0.nextAllocId + 1
      allocations := m0.allocations ++ [allocMut] }
  let stMut : PaddedSymMemState :=
    { stPinned with mem := memMut }
  let allocDealloc : Allocation := { allocMut with live := false }
  let memDealloc : MemoryState :=
    { nextAllocId := m0.nextAllocId + 1
      allocations := m0.allocations ++ [allocDealloc] }
  let newStructRound : U8U32Struct := ⟨UInt8.ofNat aInit, BitVec.ofNat 32 bNew⟩
  let newSymValEq : paddedU8U32MemCodec.encodeToSymVal newStructRound = newSymVal := rfl
  let stReabsorbed : PaddedSymMemState :=
    { sym :=
        { locals := st0.sym.locals
          loans := [⟨0, .activeMut, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
          regionGroups := []
          regionDeposits := []
          spatial := []
          nextSpatialTag := 2 }
      mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
      mirLocals := [.immediate (some .unit), .indirect place]
      mem := memMut
      memBlocks := []
      promotedLocals := [entryPinned] }
  let stEndSym : SymState Val :=
    { locals := [⟨.unit, .unborrowed⟩, ⟨newSymVal, .unborrowed⟩]
      loans := [⟨0, .ended, ⟨newSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩]
      regionGroups := []
      regionDeposits := []
      spatial := []
      nextSpatialTag := 2 }
  let stDeadSym : SymState Val :=
    { stEndSym with locals := [⟨.unit, .unborrowed⟩, ⟨.unit, .unborrowed⟩] }
  let stDealloc : PaddedSymMemState :=
    { sym := stDeadSym
      mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
      mirLocals := [.immediate (some .unit), .dead]
      mem := memDealloc
      memBlocks := []
      promotedLocals := [] }
  have hFindUninit :
      execFindAllocation m0.nextAllocId (m0.allocations ++ [allocUninit]) = some allocUninit :=
    execFindAllocation_append_lt m0.allocations allocUninit hFresh
  have hReplPinned :
      execReplaceAllocation allocPinned (m0.allocations ++ [allocUninit]) =
        m0.allocations ++ [allocPinned] :=
    execReplaceAllocation_append_lt m0.allocations allocUninit allocPinned hFresh rfl
  have hFindPinned :
      execFindAllocation m0.nextAllocId (m0.allocations ++ [allocPinned]) = some allocPinned :=
    execFindAllocation_append_lt m0.allocations allocPinned hFresh
  have hReplMut :
      execReplaceAllocation allocMut (m0.allocations ++ [allocPinned]) =
        m0.allocations ++ [allocMut] :=
    execReplaceAllocation_append_lt m0.allocations allocPinned allocMut hFresh rfl
  have hFindMut :
      execFindAllocation m0.nextAllocId (m0.allocations ++ [allocMut]) = some allocMut :=
    execFindAllocation_append_lt m0.allocations allocMut hFresh
  have hReplDealloc :
      execReplaceAllocation allocDealloc (m0.allocations ++ [allocMut]) =
        m0.allocations ++ [allocDealloc] :=
    execReplaceAllocation_append_lt m0.allocations allocMut allocDealloc hFresh rfl
  have hFreeze :
      freezePaddedToMem u8U32Ctx2 0 paddedU8U32MemCodec
        paddedU8U32MemCodec_lawful st0 =
        .ok stPinned := by
    have hNotUniq : (!hasUniqueLoanId 0 st0.sym.loans) = false := rfl
    have hFindL :
        findLoan 0 st0.sym.loans =
          some ⟨0, .activeMut, ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩ := rfl
    have hPureBad :
        (!((@LoanPhase.activeMut Val).isActiveMut &&
           isUnborrowed PermTree.unborrowed &&
           noActiveChildLoanEdgesIn mirValAlg 0 st0.sym.loans &&
           noActiveChildRegionEdges 0 st0.sym.regionGroups &&
           Nat.beq (countPaddedBlocksForLoan 0 st0.memBlocks) 0 &&
           !hasPaddedBlockId st0.sym.nextSpatialTag st0.memBlocks &&
           Nat.beq (countBlocksForLoan 0 st0.sym.spatial) 0 &&
           !hasSpatialBlockId st0.sym.nextSpatialTag st0.sym.spatial)) = false := rfl
    have hValReflTrue : mirValBeqAt 8 initSymVal initSymVal = true := by
      change
        (((true && true) &&
          Nat.beq (BitVec.ofNat 128 (UInt8.ofNat aInit).toNat).toNat
                  (BitVec.ofNat 128 (UInt8.ofNat aInit).toNat).toNat) &&
         (((true && true) &&
           Nat.beq (BitVec.ofNat 128 (BitVec.ofNat 32 bInit).toNat).toNat
                   (BitVec.ofNat 128 (BitVec.ofNat 32 bInit).toNat).toNat) &&
          true)) = true
      rw [natBeq_refl (BitVec.ofNat 128 (UInt8.ofNat aInit).toNat).toNat]
      rw [natBeq_refl (BitVec.ofNat 128 (BitVec.ofNat 32 bInit).toNat).toNat]
      rfl
    have hValMatch : (!mirValBeqAt 8 initSymVal initSymVal) = false := by
      rw [hValReflTrue]
      rfl
    have hEncOk :
        (!(mirValBeqAt 8 (paddedU8U32MemCodec.encodeToSymVal initStruct) initSymVal &&
           valCompatWithTargetSpec initSymVal paddedU8U32MemCodec.targetTy &&
           Nat.beq (paddedU8U32MemCodec.encodeValToMem initStruct).length
             paddedU8U32MemCodec.layout.size &&
           Nat.beq paddedU8U32MemCodec.padMask.length paddedU8U32MemCodec.layout.size &&
           nonPadBytesInitialized paddedU8U32MemCodec.padMask
             (paddedU8U32MemCodec.encodeValToMem initStruct) &&
           paddedU8U32MemCodec.provCheck (paddedU8U32MemCodec.encodeValToMem initStruct) &&
           valAndBytesMatchTargetSpec true paddedU8U32MemCodec.targetTy initSymVal
             (paddedU8U32MemCodec.encodeValToMem initStruct))) =
          false := by
      change
        (!(mirValBeqAt 8 initSymVal initSymVal &&
           valCompatWithTargetSpec initSymVal paddedU8U32MemCodec.targetTy &&
           Nat.beq (paddedU8U32Encode initStruct).length 8 &&
           Nat.beq u8PadU32Mask.length 8 &&
           nonPadBytesInitialized u8PadU32Mask (paddedU8U32Encode initStruct) &&
           true &&
           valAndBytesMatchTargetSpec true paddedU8U32MemCodec.targetTy initSymVal
             (paddedU8U32Encode initStruct))) = false
      rw [hValReflTrue, hInitCompat, hInitRawLen, hInitNonPad, hInitBytesMatch]
      rfl
    have hLenZero : Nat.beq initRawBytes.length 0 = false := by
      change Nat.beq (paddedU8U32Encode initStruct).length 0 = false
      rw [hInitRawLen]
      rfl
    have hAllocOk :
        (!allocUninit.live || !execIsInBounds allocUninit 0 initRawBytes.length ||
          !execIsAligned allocUninit 0 2) = false := by
      dsimp only [allocUninit, execIsInBounds, execIsAligned, initRawBytes]
      rw [hInitRawLen]
      rfl
    have hBytesTakeDrop :
        allocUninit.bytes.take 0 ++ initRawBytes ++
          allocUninit.bytes.drop (0 + initRawBytes.length) = initRawBytes := by
      dsimp only [allocUninit, initRawBytes]
      rw [hInitRawLen]
      exact listAppend_nil_right (paddedU8U32Encode initStruct)
    have hFreshIdOk : (!freshPromotedAllocId 1 m0.nextAllocId st0) = false := by
      dsimp only [freshPromotedAllocId, st0, allocExclusivelyOwnedByLocal,
        anyBlockUsesAlloc, indirectLocalsUseAlloc, anyPromotedEntryUsesAlloc,
        otherPromotedEntryUsesAlloc, otherLocalUsesAlloc, otherSymLocalUsesAlloc,
        activeLoanValUsesAlloc, backTargetUsesAlloc, BackTarget.direct,
        pureSpatialUsesAlloc, regionDepositsUseAlloc, activeRegionGroupExists,
        valFreeOfAllocId, natFold, Nat.recCompiled, initSymVal,
        paddedU8U32MemCodec, paddedU8U32ToSymVal, LoanPhase.isEnded,
        mirListGet?, List.foldr]
      rw [execFindAllocation_none_of_lt m0.allocations m0.nextAllocId hFresh,
        otherLiveAllocRefsAlloc_false_of_provLt m0.allocations m0.nextAllocId hProvFresh,
        anyAllocBytesRefAlloc_false_of_provLt m0.allocations m0.nextAllocId hProvFresh]
      rfl
    have hCtx0 : (!specsMatchBodyCtx u8U32Ctx2 st0.mirLocalTypes ||
        !Nat.beq st0.mirLocalTypes.length st0.mirLocals.length) = false := rfl
    dsimp only [freezePaddedToMem]
    rw [ite_bool_false hCtx0]
    rw [ite_bool_false hNotUniq, hFindL]
    dsimp only
    rw [ite_bool_false hPureBad]
    dsimp only [loanDirectLocal?, BackTarget.direct]
    have hGetTy :
        mirListGet? st0.mirLocalTypes 1 = some paddedU8U32MemCodec.targetTy := rfl
    rw [hGetTy]
    dsimp only
    rw [ite_bool_false
      (rfl : (!spatialTargetSpecBeq paddedU8U32MemCodec.targetTy
        paddedU8U32MemCodec.targetTy) = false)]
    rw [ite_bool_false (rfl : (!ownerLocalExclusivelyHeldByLoan 1 0 st0.sym) = false)]
    rw [hDecSymInit]
    dsimp only
    rw [ite_bool_false hEncOk]
    dsimp only [st0, mirListGet?, List.foldr]
    rw [ite_bool_false hValMatch,
      ite_bool_false (rfl : hasPromotedLocalEntry 1 [] = false),
      ite_bool_false hFreshIdOk]
    dsimp only [paddedU8U32MemCodec, execAllocateStack, execReserveAllocId, execWriteBytes]
    have hUninitEq :
        ({ allocId := m0.nextAllocId, alignLog2 := 2, mutability := .mut,
           bytes := List.replicate 8 .uninit, live := true } : Allocation) = allocUninit := rfl
    rw [hUninitEq, hFindUninit]
    dsimp only
    rw [ite_bool_false hLenZero, ite_bool_false hAllocOk]
    rw [hBytesTakeDrop]
    have hAllocEq :
        ({ allocId := m0.nextAllocId, alignLog2 := 2, mutability := .mut,
           bytes := initRawBytes, live := true } : Allocation) = allocPinned := rfl
    rw [hAllocEq, hReplPinned]
    rfl
  have hWritePinned :
      execWriteBytes memPinned ⟨place.allocId, 4⟩ 2 bNewMemBytes = .ok memMut := by
    have hBLen : bNewMemBytes.length = 4 := by
      dsimp only [bNewMemBytes]
      rw [listLength_map]
      exact execEncodeUInt_length execProfileTargetEndian 4 bNew
    have hLenZero : Nat.beq bNewMemBytes.length 0 = false := by
      rw [hBLen]
      rfl
    have hInit8 : initRawBytes.length = 8 := hInitRawLen
    have hWrOk :
        (!allocPinned.live || !execIsInBounds allocPinned 4 bNewMemBytes.length ||
          !execIsAligned allocPinned 4 2) = false := by
      dsimp only [allocPinned, execIsInBounds, execIsAligned]
      rw [hInit8, hBLen]
      rfl
    have hSpliceBytes :
        (allocPinned.bytes.take 4 ++ bNewMemBytes ++
          allocPinned.bytes.drop (4 + bNewMemBytes.length)) = mutRawBytes := by
      dsimp only [allocPinned, initRawBytes, paddedU8U32Encode]
      rw [hBLen]
      cases hOld : execEncodeUInt execProfileTargetEndian 4 initStruct.bVal.toNat with
      | nil =>
        have hL := execEncodeUInt_length execProfileTargetEndian 4 initStruct.bVal.toNat
        rw [hOld] at hL; nomatch hL
      | cons _ r1 =>
        cases r1 with
        | nil =>
          have hL := execEncodeUInt_length execProfileTargetEndian 4 initStruct.bVal.toNat
          rw [hOld] at hL; nomatch hL
        | cons _ r2 =>
          cases r2 with
          | nil =>
            have hL := execEncodeUInt_length execProfileTargetEndian 4 initStruct.bVal.toNat
            rw [hOld] at hL; nomatch hL
          | cons _ r3 =>
            cases r3 with
            | nil =>
              have hL := execEncodeUInt_length execProfileTargetEndian 4 initStruct.bVal.toNat
              rw [hOld] at hL; nomatch hL
            | cons _ r4 =>
              cases r4 with
              | cons _ _ =>
                have hL := execEncodeUInt_length execProfileTargetEndian 4 initStruct.bVal.toNat
                rw [hOld] at hL; nomatch hL
              | nil =>
                change
                  [AllocByte.init initStruct.aByte none, .uninit, .uninit, .uninit] ++
                    bNewMemBytes ++ [] = mutRawBytes
                rw [listAppend_nil_right]
    dsimp only [execWriteBytes, memPinned, place]
    rw [hFindPinned]
    dsimp only
    rw [ite_bool_false hLenZero, ite_bool_false hWrOk]
    dsimp only [allocPinned]
    rw [hSpliceBytes]
    have hAllocEq :
        ({ allocId := m0.nextAllocId, alignLog2 := 2, mutability := .mut,
           bytes := mutRawBytes, live := true } : Allocation) = allocMut := rfl
    rw [hAllocEq, hReplMut]
  have hMutate :
      mutatePaddedInMem u8U32Ctx2 1 1 4 2 bNewMemBytes stPinned = .ok stMut := by
    have hBLen : bNewMemBytes.length = 4 := by
      dsimp only [bNewMemBytes]
      rw [listLength_map]
      exact execEncodeUInt_length execProfileTargetEndian 4 bNew
    have hFindBlk : findPaddedSpatialBlock stPinned.memBlocks 1 = some (blkPinned, []) := rfl
    have hNotUniqP : (!hasUniqueLoanId blkPinned.originLoan stPinned.sym.loans) = false := rfl
    have hFindLP :
        findLoan blkPinned.originLoan stPinned.sym.loans =
          some ⟨0, .spatialPinned 1 witness0, ⟨initSymVal, .unborrowed⟩,
            .direct (.localReg 1) []⟩ := rfl
    have hSymCohP :
        (!pinnedLoanSymCoherent
            ⟨0, .spatialPinned 1 witness0, ⟨initSymVal, .unborrowed⟩,
              ⟨[.direct (.localReg 1) []]⟩⟩
            1 blkPinned [] stPinned.sym) = false := rfl
    have hMetaBad :
        (!(Nat.beq 1 1 &&
           Nat.beq blkPinned.provenanceTag 1 &&
           Nat.beq blkPinned.provenanceTag 1 &&
           witnessMatchesBlock witness0 1 blkPinned &&
           Nat.beq 8 blkPinned.layout.size &&
           Nat.beq 2 blkPinned.layout.alignLog2 &&
           (match blkPinned.perm with | .readWrite => true | .readOnly => false) &&
           Nat.beq blkPinned.activeSubSplits 0 &&
           Nat.ble (4 + bNewMemBytes.length) blkPinned.layout.size &&
           Nat.ble 2 blkPinned.layout.alignLog2 &&
           Nat.beq (Nat.mod (blkPinned.place.offset + 4) (Nat.pow 2 2)) 0)) = false := by
      dsimp only [blkPinned, witnessMatchesBlock, witness0, paddedLoanWitnessCodec,
        paddedU8U32MemCodec, place]
      rw [natBeq_refl m0.nextAllocId, hBLen]
      rfl
    have hSlotBad :
        (!slotMatchesIndirection stPinned.mirLocals 1 blkPinned.place ||
         otherPromotedEntryUsesAlloc 1 blkPinned.place.allocId
           stPinned.promotedLocals ||
         otherIndirectLocalUsesAlloc 1 blkPinned.place.allocId
           stPinned.mirLocals) = false := by
      dsimp only [slotMatchesIndirection, otherPromotedEntryUsesAlloc,
        otherIndirectLocalUsesAlloc, stPinned, entryPinned, blkPinned,
        place, mirListGet?, List.foldr]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hSliceOkP :
        (!liveMutSliceValid stPinned.mem blkPinned.place blkPinned.layout) = false := by
      dsimp only [liveMutSliceValid, stPinned, memPinned, blkPinned, place,
        execIsInBounds, execIsAligned]
      rw [hFindPinned]
      dsimp only [allocPinned, initRawBytes]
      rw [hInitRawLen]
      rfl
    have hReadInit :
        execReadBytes stPinned.mem blkPinned.place blkPinned.layout.size
          blkPinned.layout.alignLog2 = .ok initRawBytes := by
      have hRdOk :
          (!allocPinned.live || !execIsInBounds allocPinned place.offset 8 ||
            !execIsAligned allocPinned place.offset 2) = false := by
        dsimp only [allocPinned, execIsInBounds, execIsAligned, place, initRawBytes]
        rw [hInitRawLen]
        rfl
      dsimp only [execReadBytes, stPinned, memPinned, blkPinned, place]
      rw [hFindPinned]
      dsimp only
      rw [ite_bool_false (rfl : Nat.beq 8 0 = false), ite_bool_false hRdOk, listDrop_zero]
      exact congrArg Except.ok (listTake_of_len_eq hInitRawLen)
    have hProvSubNone :
        ∀ (bs : List UInt8) (allowed : List AllocByte),
          bytesProvSubset (bs.map (fun b => AllocByte.init b none)) allowed = true := by
      intro bs allowed
      induction bs with
      | nil => rfl
      | cons _ tl ih => exact ih
    have hProvBad :
        (!bytesProvSubset bNewMemBytes
          (nonPadBytesOfMask u8PadU32Mask initRawBytes)) = false := by
      dsimp only [bNewMemBytes]
      rw [hProvSubNone (execEncodeUInt execProfileTargetEndian 4 bNew)
        (nonPadBytesOfMask u8PadU32Mask initRawBytes)]
      rfl
    dsimp only [mutatePaddedInMem]
    rw [ite_bool_false
      (rfl : (!specsMatchBodyCtx u8U32Ctx2 stPinned.mirLocalTypes ||
        !Nat.beq stPinned.mirLocalTypes.length stPinned.mirLocals.length) = false)]
    rw [hFindBlk]
    dsimp only
    rw [ite_bool_false hNotUniqP, hFindLP]
    dsimp only [loanDirectLocal?, BackTarget.direct]
    rw [ite_bool_false hSymCohP]
    have hGetTyM : mirListGet? stPinned.mirLocalTypes 1 = some u8U32TargetSpec := rfl
    rw [hGetTyM]
    dsimp only
    have hLayMaskM : targetSpecLayoutAndMask u8U32TargetSpec = some (⟨8, 2⟩, u8PadU32Mask) := rfl
    rw [hLayMaskM]
    dsimp only
    rw [ite_bool_false hMetaBad, ite_bool_false hSlotBad,
      ite_bool_false hSliceOkP, hReadInit]
    dsimp only
    rw [ite_bool_false hProvBad]
    dsimp only [stPinned, blkPinned]
    change (match execWriteBytes memPinned ⟨place.allocId, 4⟩ 2 bNewMemBytes with
      | .error _ => EvalOutcome.fail
      | .ok mem' => EvalOutcome.ok { stPinned with mem := mem' }) =
      EvalOutcome.ok stMut
    rw [hWritePinned]
  have hRealWrite :
      Trusted.MirSemantics.writeBytes stPinned.mem ⟨place.allocId, 4⟩ 2 bNewMemBytes =
        .ok stMut.mem := by
    rw [← execWriteBytes_eq]
    exact hWritePinned
  have hFindMutReal :
      findAllocation place.allocId stMut.mem.allocations =
        some ⟨place.allocId, 2, .mut, mutRawBytes, true⟩ := by
    rw [← execFindAllocation_eq]
    exact hFindMut
  have hNewLen : mutRawBytes.length = 8 := by
    dsimp only [mutRawBytes, bNewMemBytes]
    rw [listLength_append, listLength_map, execEncodeUInt_length execProfileTargetEndian 4 bNew]
    rfl
  have hEncLen : (execEncodeUInt execProfileTargetEndian 4 bNew).length = 4 :=
    execEncodeUInt_length execProfileTargetEndian 4 bNew
  have hReadMut :
      execReadBytes stMut.mem place 8 2 = .ok mutRawBytes := by
    have hRdOk :
        (!allocMut.live || !execIsInBounds allocMut place.offset 8 ||
          !execIsAligned allocMut place.offset 2) = false := by
      dsimp only [allocMut, execIsInBounds, execIsAligned, place]
      rw [hNewLen]
      rfl
    dsimp only [execReadBytes, stMut, memMut, place]
    rw [hFindMut]
    dsimp only
    rw [ite_bool_false (rfl : Nat.beq 8 0 = false), ite_bool_false hRdOk, listDrop_zero]
    exact congrArg Except.ok (listTake_of_len_eq hNewLen)
  have hNonPadMut : nonPadBytesInitialized u8PadU32Mask mutRawBytes = true := by
    dsimp only [mutRawBytes, bNewMemBytes]
    change nonPadBytesInitialized [false, false, false, false]
      ((execEncodeUInt execProfileTargetEndian 4 bNew).map (fun b => AllocByte.init b none)) = true
    exact nonPad_map_init4 _ hEncLen
  have hPadUninit :
      Trusted.MirSemantics.readBytes stMut.mem ⟨place.allocId, 1⟩ 3 0 =
        .ok [.uninit, .uninit, .uninit] := by
    have hPadOk :
        (!allocMut.live || !execIsInBounds allocMut 1 3 || !execIsAligned allocMut 1 0) = false := by
      dsimp only [allocMut, execIsInBounds, execIsAligned]
      rw [hNewLen]
      rfl
    rw [← execReadBytes_eq]
    dsimp only [execReadBytes, stMut, memMut, place]
    rw [hFindMut]
    dsimp only
    rw [ite_bool_false (rfl : Nat.beq 3 0 = false), ite_bool_false hPadOk]
    rfl
  have hLoadA :
      Trusted.MirSemantics.loadIndirect stMut.mem (.int .i8 false) ⟨place.allocId, 0⟩ =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 aInit⟩)) :=
    paddedStruct_loadFieldA stMut.mem place aInit bNew hA hFindMutReal rfl
  have hLoadB :
      Trusted.MirSemantics.loadIndirect stMut.mem (.int .i32 false) ⟨place.allocId, 4⟩ =
        .ok (some (.scalar ⟨.i32, false, BitVec.ofNat 128 bNew⟩)) :=
    paddedStruct_loadFieldB stMut.mem place aInit bNew hBNew hFindMutReal
  have hEncNewEqMut : paddedU8U32Encode newStruct = mutRawBytes := by
    have hBLt : bNew < 4294967296 := natLt_of_blt bNew 4294967296 hBNew
    have hPow32 : Nat.pow 2 32 = 4294967296 := rfl
    have hBLt32 : bNew < Nat.pow 2 32 := by rw [hPow32]; exact hBLt
    have hBv32 : (BitVec.ofNat 32 bNew).toNat = bNew := by
      change Nat.mod bNew (Nat.pow 2 32) = bNew
      exact natMod_eq_of_lt hBLt32
    dsimp only [paddedU8U32Encode, newStruct, mutRawBytes, bNewMemBytes]
    rw [hBv32]
  have hReabsorb :
      reabsorbPaddedFromMem u8U32Ctx2 0 stMut =
        .ok stReabsorbed := by
    have hDecMut : paddedU8U32Decode mutRawBytes = some newStructRound := by
      dsimp only [mutRawBytes, bNewMemBytes]
      rw [paddedU8U32Decode_of_raw4 (UInt8.ofNat aInit) .uninit .uninit .uninit _ hEncLen]
      rw [u32Bytes_dec_inj bNew hBNew]
    have hNotUniq : (!hasUniqueLoanId 0 stMut.sym.loans) = false := rfl
    have hFindL :
        findLoan 0 stMut.sym.loans =
          some ⟨0, .spatialPinned 1 witness0,
            ⟨initSymVal, .unborrowed⟩, .direct (.localReg 1) []⟩ := rfl
    have hFindB :
        findPaddedSpatialBlock stMut.memBlocks 1 = some (blkPinned, []) := rfl
    have hSymCohM :
        (!pinnedLoanSymCoherent
            ⟨0, .spatialPinned 1 witness0, ⟨initSymVal, .unborrowed⟩,
              ⟨[.direct (.localReg 1) []]⟩⟩
            1 blkPinned [] stMut.sym) = false := rfl
    have hPinBad :
        (!(Nat.beq blkPinned.originLoan 0 &&
           Nat.beq blkPinned.provenanceTag 1 &&
           witnessMatchesBlock witness0 1 blkPinned &&
           Nat.beq 8 blkPinned.layout.size &&
           Nat.beq 2 blkPinned.layout.alignLog2 &&
           (match blkPinned.perm with | .readWrite => true | .readOnly => false) &&
           Nat.beq blkPinned.activeSubSplits 0)) = false := by
      dsimp only [blkPinned, witnessMatchesBlock, witness0, paddedLoanWitnessCodec,
        paddedU8U32MemCodec, place, stMut, stPinned]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hSlotBad :
        (!slotMatchesIndirection stMut.mirLocals 1 blkPinned.place ||
         otherPromotedEntryUsesAlloc 1 blkPinned.place.allocId
           stMut.promotedLocals ||
         otherIndirectLocalUsesAlloc 1 blkPinned.place.allocId
           stMut.mirLocals) = false := by
      dsimp only [slotMatchesIndirection, otherPromotedEntryUsesAlloc,
        otherIndirectLocalUsesAlloc, stMut, stPinned, entryPinned,
        blkPinned, place, mirListGet?, List.foldr]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hSliceOkM :
        (!liveMutSliceValid stMut.mem blkPinned.place blkPinned.layout) = false := by
      dsimp only [liveMutSliceValid, stMut, memMut, blkPinned, place,
        execIsInBounds, execIsAligned]
      rw [hFindMut]
      dsimp only [allocMut]
      rw [hNewLen]
      rfl
    have hMutBytesMatchFalse :
        (!valAndBytesMatchTargetSpec false u8U32TargetSpec
          (paddedU8U32ToSymVal newStructRound) mutRawBytes) = false := by
      have hTrue :
          valAndBytesMatchTargetSpec true u8U32TargetSpec
            (paddedU8U32ToSymVal newStruct) (paddedU8U32Encode newStruct) =
            true :=
        (hLawful.2.2.1 newStruct).2.2.2.2.1
      have hFalse :=
        valAndBytesMatchTargetSpec_false_of_true u8U32TargetSpec
          (paddedU8U32ToSymVal newStruct) (paddedU8U32Encode newStruct) hTrue
      rw [hEncNewEqMut] at hFalse
      change (!valAndBytesMatchTargetSpec false u8U32TargetSpec
        (paddedU8U32ToSymVal newStruct) mutRawBytes) = false
      rw [hFalse]
      rfl
    have hWitnessDec :
        witness0.decode [.uninit, .init (.bytes mutRawBytes)] = some newSymVal := by
      dsimp only [witness0, paddedLoanWitnessCodec, paddedU8U32MemCodec]
      have hNonPadGuard : (!nonPadBytesInitialized u8PadU32Mask mutRawBytes) = false := by
        rw [hNonPadMut]; rfl
      rw [ite_bool_false hNonPadGuard]
      rw [ite_bool_false (rfl : (!true) = false)]
      rw [hDecMut]
      dsimp only
      rw [ite_bool_false hMutBytesMatchFalse]
      exact congrArg Option.some newSymValEq
    have hNonPadReab : (!nonPadBytesInitialized u8PadU32Mask mutRawBytes) = false := by
      rw [hNonPadMut]; rfl
    have hCompatReab : (!valCompatWithTargetSpec newSymVal u8U32TargetSpec) = false := by
      have hC : valCompatWithTargetSpec newSymVal paddedU8U32MemCodec.targetTy = true :=
        (hLawful.2.2.1 newStruct).2.2.2.1
      change (!valCompatWithTargetSpec newSymVal paddedU8U32MemCodec.targetTy) = false
      rw [hC]; rfl
    have hMatchReab :
        (!valAndBytesMatchTargetSpec false u8U32TargetSpec newSymVal mutRawBytes) = false := by
      rw [← newSymValEq]
      exact hMutBytesMatchFalse
    dsimp only [reabsorbPaddedFromMem]
    rw [ite_bool_false
      (rfl : (!specsMatchBodyCtx u8U32Ctx2 stMut.mirLocalTypes ||
        !Nat.beq stMut.mirLocalTypes.length stMut.mirLocals.length) = false)]
    rw [ite_bool_false hNotUniq, hFindL]
    dsimp only [loanDirectLocal?, BackTarget.direct]
    rw [hFindB]
    dsimp only
    rw [ite_bool_false hSymCohM]
    have hGetTyR : mirListGet? stMut.mirLocalTypes 1 = some u8U32TargetSpec := rfl
    rw [hGetTyR]
    dsimp only
    have hLayMaskR : targetSpecLayoutAndMask u8U32TargetSpec = some (⟨8, 2⟩, u8PadU32Mask) := rfl
    rw [hLayMaskR]
    dsimp only
    rw [ite_bool_false hPinBad, ite_bool_false hSlotBad,
      ite_bool_false hSliceOkM]
    have hReadBlk :
        execReadBytes stMut.mem blkPinned.place blkPinned.layout.size blkPinned.layout.alignLog2 =
          .ok mutRawBytes := hReadMut
    rw [hReadBlk]
    dsimp only
    rw [hWitnessDec]
    dsimp only
    rw [ite_bool_false hNonPadReab, ite_bool_false hCompatReab,
      ite_bool_false hMatchReab]
    have hRepZero :
        (!replaceableVal mirValAlg stMut.sym.loans initSymVal newSymVal) = false := rfl
    rw [ite_bool_false hRepZero]
    rfl
  have hEndSym :
      endLoanInState mirValAlg 0 stReabsorbed.sym =
        .ok stEndSym := rfl
  have hEndPadded :
      endPaddedLoan u8U32Ctx2 0 stReabsorbed =
        .ok { stReabsorbed with sym := stEndSym } := by
    have hDecSymNew :
        paddedU8U32MemCodec.decodeFromSymVal newSymVal = some newStruct :=
      (hLawful.2.2.1 newStruct).2.2.2.2.2.2
    have hNewValRefl : mirValBeqAt 8 newSymVal newSymVal = true := by
      change
        (((true && true) &&
          Nat.beq (BitVec.ofNat 128 (UInt8.ofNat aInit).toNat).toNat
                  (BitVec.ofNat 128 (UInt8.ofNat aInit).toNat).toNat) &&
         (((true && true) &&
           Nat.beq (BitVec.ofNat 128 (BitVec.ofNat 32 bNew).toNat).toNat
                   (BitVec.ofNat 128 (BitVec.ofNat 32 bNew).toNat).toNat) &&
          true)) = true
      rw [natBeq_refl (BitVec.ofNat 128 (UInt8.ofNat aInit).toNat).toNat]
      rw [natBeq_refl (BitVec.ofNat 128 (BitVec.ofNat 32 bNew).toNat).toNat]
      rfl
    have hCompatNew :
        valCompatWithTargetSpec newSymVal paddedU8U32MemCodec.targetTy = true :=
      (hLawful.2.2.1 newStruct).2.2.2.1
    have hBytesMatchNew :
        valAndBytesMatchTargetSpec true paddedU8U32MemCodec.targetTy newSymVal
          (paddedU8U32Encode newStruct) = true :=
      (hLawful.2.2.1 newStruct).2.2.2.2.1
    have hEncSymToMem :
        encodeSymOfCodec paddedU8U32MemCodec newSymVal = some mutRawBytes := by
      dsimp only [encodeSymOfCodec]
      rw [hDecSymNew]
      dsimp only
      change
        (if mirValBeqAt 8 newSymVal newSymVal &&
            valCompatWithTargetSpec newSymVal paddedU8U32MemCodec.targetTy &&
            true &&
            valAndBytesMatchTargetSpec true paddedU8U32MemCodec.targetTy
              newSymVal (paddedU8U32Encode newStruct) then
           some (paddedU8U32Encode newStruct)
         else none) = some mutRawBytes
      rw [hNewValRefl, hCompatNew, hBytesMatchNew, Bool.true_and,
        Bool.true_and, Bool.true_and, ite_bool_true rfl, hEncNewEqMut]
    have hSameMut : sameAtNonPad u8PadU32Mask mutRawBytes mutRawBytes = true := by
      dsimp only [mutRawBytes, bNewMemBytes]
      cases hXs : execEncodeUInt execProfileTargetEndian 4 bNew with
      | nil => rw [hXs] at hEncLen; nomatch hEncLen
      | cons x0 r1 =>
        cases r1 with
        | nil => rw [hXs] at hEncLen; nomatch hEncLen
        | cons x1 r2 =>
          cases r2 with
          | nil => rw [hXs] at hEncLen; nomatch hEncLen
          | cons x2 r3 =>
            cases r3 with
            | nil => rw [hXs] at hEncLen; nomatch hEncLen
            | cons x3 r4 =>
              cases r4 with
              | cons _ _ => rw [hXs] at hEncLen; nomatch hEncLen
              | nil =>
                dsimp only [HAppend.hAppend, Append.append, List.append,
                  List.map, sameAtNonPad, u8PadU32Mask, allocByteBeq,
                  optAllocIdBeq, List.foldr]
                rw [natBeq_refl (UInt8.ofNat aInit).toNat,
                  natBeq_refl x0.toNat, natBeq_refl x1.toNat,
                  natBeq_refl x2.toNat, natBeq_refl x3.toNat]
                rfl
    have hFindUniq1 :
        findUniquePromotedLocalEntry [entryPinned] 1 = some (entryPinned, []) :=
      rfl
    have hEveryTrk :
        everyIndirectSlotTracked [.immediate (some .unit), .indirect place]
          [entryPinned] = true := by
      dsimp only [everyIndirectSlotTracked, List.foldr]
      rw [hFindUniq1]
      dsimp only [entryPinned, place]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hEveryCoh :
        everySlotCoherentWithSym [.mirTy .unit, paddedU8U32MemCodec.targetTy]
          [.immediate (some .unit), .indirect place]
          [entryPinned] [] stEndSym = true := by
      dsimp only [everySlotCoherentWithSym, noActiveBorrowTargetsDeadOrUninit,
        stEndSym, LoanPhase.isEnded, List.foldr]
      rw [hFindUniq1]
      dsimp only [entryPinned, place]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hTrkOk :
        (!specsMatchBodyCtx u8U32Ctx2
            [.mirTy .unit, paddedU8U32MemCodec.targetTy] ||
          ![SpatialTargetSpec.mirTy .unit, paddedU8U32MemCodec.targetTy].length.beq
            [LocalSlot.immediate (some .unit), LocalSlot.indirect place].length ||
          !stEndSym.locals.length.beq
            [LocalSlot.immediate (some .unit), LocalSlot.indirect place].length ||
          !everyIndirectSlotTracked [.immediate (some .unit), .indirect place]
            [entryPinned]) = false := by
      rw [hEveryTrk]
      rfl
    have hSlotMatch :
        slotMatchesIndirection [.immediate (some .unit), .indirect place] 1 place =
          true := by
      dsimp only [slotMatchesIndirection, mirListGet?, List.foldr, place]
      rw [natBeq_refl m0.nextAllocId]
      rfl
    have hSliceValid :
        liveMutSliceValid memMut place ⟨8, 2⟩ = true := by
      dsimp only [liveMutSliceValid, memMut, place, execIsInBounds, execIsAligned]
      rw [hFindMut]
      dsimp only [allocMut]
      rw [hNewLen]
      rfl
    have hSlotSliceOk :
        (!slotMatchesIndirection [.immediate (some .unit), .indirect place] 1 place ||
          !liveMutSliceValid memMut place ⟨8, 2⟩) = false := by
      rw [hSlotMatch, hSliceValid]
      rfl
    have hBytesMatchMutFalse :
        valAndBytesMatchTargetSpec false paddedU8U32MemCodec.targetTy newSymVal
          mutRawBytes = true := by
      have hFalse :=
        valAndBytesMatchTargetSpec_false_of_true paddedU8U32MemCodec.targetTy
          newSymVal (paddedU8U32Encode newStruct) hBytesMatchNew
      rw [hEncNewEqMut] at hFalse
      exact hFalse
    have hSameCheck :
        (nonPadBytesInitialized u8PadU32Mask mutRawBytes &&
          sameAtNonPad u8PadU32Mask mutRawBytes mutRawBytes &&
          valAndBytesMatchTargetSpec false paddedU8U32MemCodec.targetTy
            newSymVal mutRawBytes) = true := by
      rw [hNonPadMut, hSameMut, hBytesMatchMutFalse]
      rfl
    have hPromEntrySynced :
        promotedEntryMemSynced entryPinned
          { stReabsorbed with sym := stEndSym } = true := by
      dsimp only [promotedEntryMemSynced, otherPromotedEntryUsesAlloc,
        otherIndirectLocalUsesAlloc, stReabsorbed, entryPinned, List.foldr]
      have hGetTy1 :
          mirListGet? [.mirTy .unit, paddedU8U32MemCodec.targetTy] 1 =
            some paddedU8U32MemCodec.targetTy := rfl
      have hBeqTy :
          spatialTargetSpecBeq paddedU8U32MemCodec.targetTy
            paddedU8U32MemCodec.targetTy = true := rfl
      rw [hSlotMatch, hGetTy1]
      dsimp only
      rw [hBeqTy, hSliceValid,
        ite_bool_false (rfl : anyBlockTargetsLocal 1 [] = false)]
      have hAuth : authoritativeSymValForLocal 1 stEndSym = some newSymVal := rfl
      rw [hAuth]
      dsimp only
      rw [hEncSymToMem]
      dsimp only
      rw [ite_bool_false (rfl : Nat.beq 8 0 = false)]
      have hReadEq : execReadBytes memMut place 8 2 = .ok mutRawBytes := hReadMut
      rw [hReadEq]
      dsimp only
      rw [hSameCheck]
      rfl
    have hSyncedAll :
        allPromotedLocalsMemSynced u8U32Ctx2
          { stReabsorbed with sym := stEndSym } = true := by
      have hCtxOk : specsMatchBodyCtx u8U32Ctx2
          [.mirTy .unit, paddedU8U32MemCodec.targetTy] = true := rfl
      dsimp only [allPromotedLocalsMemSynced, stReabsorbed]
      rw [hCtxOk, hEveryCoh]
      dsimp only [List.foldr]
      have hPE :
          promotedEntryMemSynced entryPinned
            { sym := stEndSym
              mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
              mirLocals := [.immediate (some .unit), .indirect place]
              mem := memMut
              memBlocks := []
              promotedLocals := [entryPinned] } = true := hPromEntrySynced
      rw [hPE]
      rfl
    have hRefreshId :
        refreshImmediateMirLocals [.immediate (some .unit), .indirect place]
          stEndSym = [.immediate (some .unit), .indirect place] := rfl
    have hEndGuard :
        (!specsMatchBodyCtx u8U32Ctx2 stReabsorbed.mirLocalTypes ||
          !Nat.beq stReabsorbed.mirLocalTypes.length
            stReabsorbed.mirLocals.length ||
          !Nat.beq stReabsorbed.sym.locals.length
            stReabsorbed.mirLocals.length ||
          !noActiveBorrowTargetsDeadOrUninit stReabsorbed.mirLocals
            stReabsorbed.sym) = false := rfl
    dsimp only [endPaddedLoan]
    rw [ite_bool_false hEndGuard, hEndSym]
    dsimp only [syncPromotedLocalsToMem, stReabsorbed]
    rw [ite_bool_false hTrkOk, hRefreshId]
    dsimp only [List.foldr, entryPinned]
    rw [ite_bool_false hSlotSliceOk,
      ite_bool_false (rfl : anyBlockTargetsLocal 1 [] = false)]
    have hAuth : authoritativeSymValForLocal 1 stEndSym = some newSymVal := rfl
    rw [hAuth]
    dsimp only
    rw [hEncSymToMem]
    dsimp only
    rw [ite_bool_false (rfl : Nat.beq 8 0 = false)]
    have hReadEq : execReadBytes memMut place 8 2 = .ok mutRawBytes := hReadMut
    rw [hReadEq]
    dsimp only
    rw [ite_bool_true hSameCheck]
    dsimp only
    have hSyncedGoal :
        allPromotedLocalsMemSynced u8U32Ctx2
          { sym := stEndSym
            mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
            mirLocals := [.immediate (some .unit), .indirect place]
            mem := memMut
            memBlocks := []
            promotedLocals := [entryPinned] } = true := hSyncedAll
    rw [ite_bool_true hSyncedGoal]
  have hGetLocal :
      getLocal mirValAlg 1 stEndSym = some newSymVal := rfl
  have hDeallocStep :
      deallocatePromotedLocal u8U32Ctx2 1
        { stReabsorbed with sym := stEndSym } = .ok stDealloc := by
    have hOtherRefs :
        otherLiveAllocRefsAlloc m0.nextAllocId (m0.allocations ++ [allocMut]) = false :=
      otherLiveAllocRefsAlloc_append_self m0.allocations allocMut hProvFresh
    have hSafeFalse :
        (!(Nat.beq place.offset 0 &&
           isUnborrowed PermTree.unborrowed &&
           !(stEndSym.loans.foldr
               (fun le acc =>
                 (!le.phase.isEnded && backTargetMentionsLocal 1 le.target) || acc)
               false) &&
           allocExclusivelyOwnedByLocal 1 place.allocId
             { stReabsorbed with sym := stEndSym })) = false := by
      dsimp only [place, stReabsorbed, entryPinned, memMut, stEndSym,
        allocExclusivelyOwnedByLocal, anyBlockUsesAlloc,
        otherPromotedEntryUsesAlloc, otherLocalUsesAlloc,
        otherSymLocalUsesAlloc, activeLoanValUsesAlloc, pureSpatialUsesAlloc,
        regionDepositsUseAlloc, activeRegionGroupExists, valFreeOfAllocId,
        natFold, Nat.recCompiled, LoanPhase.isEnded, backTargetMentionsLocal,
        BackTarget.direct, List.foldr]
      rw [hOtherRefs]
      rfl
    have hDeallocMut : execDeallocateStack memMut place = .ok memDealloc := by
      dsimp only [execDeallocateStack, memMut, place]
      rw [hFindMut]
      dsimp only [allocMut]
      rw [hReplDealloc]
      rfl
    have hLenOk :
        (!specsMatchBodyCtx u8U32Ctx2
            [SpatialTargetSpec.mirTy .unit, paddedU8U32MemCodec.targetTy] ||
          ![SpatialTargetSpec.mirTy .unit, paddedU8U32MemCodec.targetTy].length.beq
            [LocalSlot.immediate (some .unit), LocalSlot.indirect place].length) =
          false := rfl
    dsimp only [deallocatePromotedLocal, stReabsorbed]
    rw [ite_bool_false hLenOk, ite_bool_false (rfl : Nat.beq 1 0 = false)]
    dsimp only [mirListGet?, List.foldr, stEndSym]
    change
      (if (!(Nat.beq place.offset 0 &&
             isUnborrowed PermTree.unborrowed &&
             !(stEndSym.loans.foldr
                 (fun le acc =>
                   (!le.phase.isEnded && backTargetMentionsLocal 1 le.target) || acc)
                 false) &&
             allocExclusivelyOwnedByLocal 1 place.allocId
               { stReabsorbed with sym := stEndSym })) then
         EvalOutcome.fail
       else
         match execDeallocateStack memMut place with
         | .error _ => EvalOutcome.fail
         | .ok m =>
           match mirListSet? [.immediate (some .unit), .indirect place] 1 .dead,
                 mirListSet? stEndSym.locals 1 ⟨.unit, .unborrowed⟩ with
           | some mirLocals', some symLocals' =>
             EvalOutcome.ok
               { sym := { stEndSym with locals := symLocals' }
                 mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy]
                 mirLocals := mirLocals'
                 mem := m
                 memBlocks := []
                 promotedLocals := removePromotedLocalEntry 1 [entryPinned] }
           | _, _ => EvalOutcome.fail) =
        EvalOutcome.ok stDealloc
    rw [ite_bool_false hSafeFalse, hDeallocMut]
    rfl
  have hRealDealloc :
      Trusted.MirSemantics.deallocateStack stReabsorbed.mem place = .ok stDealloc.mem := by
    rw [← execDeallocateStack_eq]
    dsimp only [execDeallocateStack, stReabsorbed, memMut, stDealloc, place]
    rw [hFindMut]
    dsimp only [allocMut]
    rw [hReplDealloc]
    rfl
  have hFramePinned :
      Trusted.MirSemantics.readBytes stPinned.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign := by
    rw [← execReadBytes_eq, ← execReadBytes_eq]
    dsimp only [execReadBytes, stPinned, memPinned]
    rw [execFindAllocation_append_ne m0.allocations allocPinned otherPlace.allocId hOtherId]
  have hFrameMut :
      Trusted.MirSemantics.readBytes stMut.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign := by
    rw [← execReadBytes_eq, ← execReadBytes_eq]
    dsimp only [execReadBytes, stMut, stPinned, memMut]
    rw [execFindAllocation_append_ne m0.allocations allocMut otherPlace.allocId hOtherId]
  have hFrameReab :
      Trusted.MirSemantics.readBytes stReabsorbed.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign :=
    hFrameMut
  have hFrameDealloc :
      Trusted.MirSemantics.readBytes stDealloc.mem otherPlace otherSize otherAlign =
        Trusted.MirSemantics.readBytes m0 otherPlace otherSize otherAlign := by
    rw [← execReadBytes_eq, ← execReadBytes_eq]
    dsimp only [execReadBytes, stDealloc, memDealloc]
    rw [execFindAllocation_append_ne m0.allocations allocDealloc otherPlace.allocId hOtherId]
  exact ⟨stPinned, stMut, stReabsorbed, stEndSym, stDealloc,
    hFreeze, rfl, hMutate, hRealWrite, hPadUninit, hLoadA, hLoadB,
    hReabsorb, rfl, hLoadA, hLoadB, hEndSym, hEndPadded, hGetLocal,
    hDeallocStep, rfl, rfl, rfl, hRealDealloc,
    hFramePinned, hFrameMut, hFrameReab, hFrameDealloc⟩

/-! ### Soundness and Fail-Closed Rejection Tests -/

/-- Initial `U8U32Struct` test value. -/
@[expose] def sampleU8U32Init : U8U32Struct := ⟨0x11, BitVec.ofNat 32
    0x22334455⟩
/-- Soundness test fixture `sampleU8U32Mut`. -/
@[expose] def sampleU8U32Mut : U8U32Struct := ⟨0x11, BitVec.ofNat 32 0x66778899⟩
/-- Soundness test fixture `sampleU8U32Other`. -/
@[expose] def sampleU8U32Other : U8U32Struct := ⟨0x22, BitVec.ofNat 32
    0xAABBCCDD⟩

/-- Computable empty `MemoryState` fixture (`nextAllocId = 1`). -/
@[expose] def execMemoryEmpty : MemoryState := ⟨1, []⟩

private theorem execMemoryEmpty_eq : execMemoryEmpty = MemoryState.empty := rfl

/-- Initial `PaddedSymMemState` fixture for `sampleU8U32Init`. -/
@[expose] def mkSampleU8U32InitState : PaddedSymMemState :=
  let v := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Init
  { sym :=
      { locals := [⟨.unit, .unborrowed⟩, ⟨v, .mutLocked 0⟩, ⟨mirEncodeRef 0 [], .unborrowed⟩]
        loans := [⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 1) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 1 }
    mirLocalTypes := [.mirTy .unit, paddedU8U32MemCodec.targetTy,
                      .mirTy (.ref .mut paddedU8U32MemCodec.targetTy.toCapturedMirTy)]
    mirLocals := [.immediate (some .unit), .immediate (some v),
                  .immediate (some (mirEncodeRef 0 []))]
    mem := execMemoryEmpty
    memBlocks := []
    promotedLocals := [] }

/-- Fail-closed `.uninit` non-padding byte overwrite assertion. -/
@[expose] def nonPadUninitCheckAt (byteOff : Nat) (fieldTy : MirTy) (fieldOff :
    Nat) : Prop :=
  Exists fun stPinned =>
  Exists fun mBad =>
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      mkSampleU8U32InitState = .ok stPinned ∧
    Trusted.MirSemantics.writeUninit stPinned.mem ⟨1, byteOff⟩ 1 0 = .ok mBad ∧
    reabsorbPaddedFromMem sampleBodyCtx 0 { stPinned with mem := mBad } = .fail ∧
    Trusted.MirSemantics.loadIndirect mBad fieldTy ⟨1, fieldOff⟩ = .ok none ∧
    Trusted.MirSemantics.evalPrimitiveOperand [fieldTy] [.indirect ⟨1, fieldOff⟩] mBad
      (.copy ⟨0, []⟩) = .error .undefined

private theorem nonPadUninitCheckAt_0 : nonPadUninitCheckAt 0 (.int .i8 false) 0 := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

private theorem nonPadUninitCheckAt_4 : nonPadUninitCheckAt 4 (.int .i32 false) 4 := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

private theorem nonPadUninitCheckAt_5 : nonPadUninitCheckAt 5 (.int .i32 false) 4 := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

private theorem nonPadUninitCheckAt_6 : nonPadUninitCheckAt 6 (.int .i32 false) 4 := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

private theorem nonPadUninitCheckAt_7 : nonPadUninitCheckAt 7 (.int .i32 false) 4 := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

/-- Verifies that overwriting any non-padding byte (`0`, `4`, `5`, `6`, `7`) of
a pinned `U8U32Struct` with `.uninit` causes both `reabsorbPaddedFromMem` and
`Trusted.MirSemantics.evalPrimitiveOperand` to fail closed. -/
theorem padded_overwrite_nonpad_uninit_fails_closed_test :
    nonPadUninitCheckAt 0 (.int .i8 false) 0 ∧
    nonPadUninitCheckAt 4 (.int .i32 false) 4 ∧
    nonPadUninitCheckAt 5 (.int .i32 false) 4 ∧
    nonPadUninitCheckAt 6 (.int .i32 false) 4 ∧
    nonPadUninitCheckAt 7 (.int .i32 false) 4 :=
  ⟨nonPadUninitCheckAt_0, nonPadUninitCheckAt_4, nonPadUninitCheckAt_5, nonPadUninitCheckAt_6, nonPadUninitCheckAt_7⟩

/-- Verifies padding non-uniqueness (`st1.mem ≠ st2.mem` across `.uninit` vs.
`0xAA` padding bytes while `reabsorbPaddedFromMem` recovers identical symbolic
states) alongside `Trusted.MirSemantics.decodeVal`, `evalPrimitiveOperand`, and
the indirect-memory mirrors `execEncodeVal`, `execStoreIndirect`, and
`execDeinitIndirect` distinguishing `.uninit` from `.init 0xAA`. -/
theorem padded_padding_non_uniqueness_and_decodeVal_uninit_test :
    Exists fun st1 =>
    Exists fun st2 =>
    Exists fun bytes1 =>
    Exists fun bytes2 =>
    Exists fun stR1 =>
    Exists fun stR2 =>
    Exists fun memStore1 =>
      freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
        mkSampleU8U32InitState = .ok st1 ∧
      Trusted.MirSemantics.writeBytes st1.mem ⟨1, 1⟩ 0
        [.init 0xAA none, .init 0xAA none, .init 0xAA none] = .ok st2.mem ∧
      st2 = { st1 with mem := st2.mem } ∧
      st1.mem ≠ st2.mem ∧
      Trusted.MirSemantics.readBytes st1.mem ⟨1, 0⟩ 8 2 = .ok bytes1 ∧
      Trusted.MirSemantics.readBytes st2.mem ⟨1, 0⟩ 8 2 = .ok bytes2 ∧
      sameAtNonPad paddedU8U32MemCodec.padMask bytes1 bytes2 = true ∧
      reabsorbPaddedFromMem sampleBodyCtx 0 st1 = .ok stR1 ∧
      reabsorbPaddedFromMem sampleBodyCtx 0 st2 = .ok stR2 ∧
      stR1.sym = stR2.sym ∧
      stR1.mirLocals = stR2.mirLocals ∧
      stR1.mem ≠ stR2.mem ∧
      execEncodeVal execProfileTargetEndian (.int .i8 false)
        (.scalar ⟨.i8, false, BitVec.ofNat 128 0xAA⟩) = .ok [.init 0xAA none] ∧
      execStoreIndirect st1.mem (.int .i8 false) ⟨1, 1⟩
        (.scalar ⟨.i8, false, BitVec.ofNat 128 0xAA⟩) = .ok memStore1 ∧
      execDeinitIndirect memStore1 (.int .i8 false) ⟨1, 1⟩ = .ok st1.mem ∧
      Trusted.MirSemantics.decodeVal execProfileTargetEndian (.int .i8 false) [.uninit] =
        .ok none ∧
      Trusted.MirSemantics.decodeVal execProfileTargetEndian (.int .i8 false) [.init 0xAA none] =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 0xAA⟩)) ∧
      Trusted.MirSemantics.evalPrimitiveOperand [.int .i8 false] [.indirect ⟨1, 1⟩]
        st1.mem (.copy ⟨0, []⟩) = .error .undefined ∧
      Trusted.MirSemantics.evalPrimitiveOperand [.int .i8 false] [.indirect ⟨1, 1⟩]
        st2.mem (.copy ⟨0, []⟩) =
          .ok (.scalar ⟨.i8, false, BitVec.ofNat 128 0xAA⟩, [.indirect ⟨1, 1⟩], st2.mem) := by
  let st1 : PaddedSymMemState :=
    match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
        mkSampleU8U32InitState with
    | .ok s => s
    | .fail => mkSampleU8U32InitState
  let mem2 : MemoryState :=
    match execWriteBytes st1.mem ⟨1, 1⟩ 0
        [.init 0xAA none, .init 0xAA none, .init 0xAA none] with
    | .ok m => m
    | .error _ => st1.mem
  let st2 : PaddedSymMemState := { st1 with mem := mem2 }
  have hWriteBytes2 :
      Trusted.MirSemantics.writeBytes st1.mem ⟨1, 1⟩ 0
        [.init 0xAA none, .init 0xAA none, .init 0xAA none] = .ok st2.mem := by
    rw [← execWriteBytes_eq]
    rfl
  have hFreeze :
      freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
        mkSampleU8U32InitState = .ok st1 := rfl
  have hNeMem12 : st1.mem ≠ st2.mem := by
    intro hEq
    have hR :
        Trusted.MirSemantics.readBytes st1.mem ⟨1, 1⟩ 1 0 =
          Trusted.MirSemantics.readBytes st2.mem ⟨1, 1⟩ 1 0 :=
      congrArg (fun m => Trusted.MirSemantics.readBytes m ⟨1, 1⟩ 1 0) hEq
    change Except.ok [AllocByte.uninit] = Except.ok [AllocByte.init 0xAA none] at hR
    injection hR with hList
    injection hList with hByte _
    nomatch hByte
  let stR1 : PaddedSymMemState :=
    match reabsorbPaddedFromMem sampleBodyCtx 0 st1 with
    | .ok s => s
    | .fail => st1
  let stR2 : PaddedSymMemState :=
    match reabsorbPaddedFromMem sampleBodyCtx 0 st2 with
    | .ok s => s
    | .fail => st2
  have hNeR12 : stR1.mem ≠ stR2.mem := hNeMem12
  exact ⟨st1, st2, _, _, stR1, stR2, _, hFreeze, hWriteBytes2, rfl, hNeMem12, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, hNeR12, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Soundness test fixture `mkProvInitState`. -/
@[expose] def mkProvInitState (expectedProv : AllocId) : PaddedSymMemState :=
  let initS : ProvPtrStruct := ⟨0x10, BitVec.ofNat 64 0x1000⟩
  let v := (provPtrPaddedMemCodec expectedProv).encodeToSymVal initS
  { sym :=
      { locals := [⟨.unit, .unborrowed⟩, ⟨v, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨v, .unborrowed⟩, .direct (.localReg 1) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 1 }
    mirLocalTypes := [.mirTy .unit, (provPtrPaddedMemCodec expectedProv).targetTy]
    mirLocals := [.immediate (some .unit), .immediate (some v)]
    mem := execMemoryEmpty
    memBlocks := []
    promotedLocals := [] }

/-- Verifies that `provPtrPaddedMemCodec` preserves pointer provenance across
non-pointer tag-byte writes and fail-closed rejects wrong-tag writes, tampered
`provenanceTag` (even when `tag` is spoofed to match `blk.provenanceTag`),
tampered `originLoan`, provenance stripping (`none`), and provenance forgery
(`some 99`). -/
theorem padded_provenance_preservation_and_forgery_rejected_test :
    let codec := provPtrPaddedMemCodec 7
    let st0 := mkProvInitState 7
    Exists fun stPinned =>
    Exists fun stTagMut =>
    Exists fun stTagReabsorbed =>
    Exists fun memClobber =>
    Exists fun memForge =>
      freezePaddedToMem (provBodyCtx 7) 0 codec (provPtrPaddedMemCodec_lawful 7) st0 = .ok stPinned ∧
      mutatePaddedInMem (provBodyCtx 7) 1 1 0 0 [.init 0x42 none] stPinned =
        .ok stTagMut ∧
      reabsorbPaddedFromMem (provBodyCtx 7) 0 stTagMut = .ok stTagReabsorbed ∧
      mutatePaddedInMem (provBodyCtx 7) 1 99 0 0 [.init 0x42 none] stPinned = .fail ∧
      mutatePaddedInMem (provBodyCtx 7) 1 99 0 0 [.init 0x42 none]
        { stPinned with
          memBlocks := stPinned.memBlocks.map (fun b => { b with provenanceTag := 99 }) } =
        .fail ∧
      reabsorbPaddedFromMem (provBodyCtx 7) 0
        { stPinned with
          memBlocks := stPinned.memBlocks.map (fun b => { b with provenanceTag := 99 }) } =
        .fail ∧
      reabsorbPaddedFromMem (provBodyCtx 7) 0
        { stPinned with
          memBlocks := stPinned.memBlocks.map (fun b => { b with originLoan := 99 }) } =
        .fail ∧
      Trusted.MirSemantics.writeBytes stPinned.mem ⟨1, 8⟩ 0 [.init 0x00 none] =
        .ok memClobber ∧
      reabsorbPaddedFromMem (provBodyCtx 7) 0
        { stPinned with mem := memClobber } = .fail ∧
      Trusted.MirSemantics.writeBytes stPinned.mem ⟨1, 8⟩ 0 [.init 0x00 (some 99)] =
        .ok memForge ∧
      reabsorbPaddedFromMem (provBodyCtx 7) 0
        { stPinned with mem := memForge } = .fail := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Verifies that while a loan is pinned in `MemoryState`, pure reads, writes,
and `endLoanInState` are blocked until `reabsorbPaddedFromMem` restores
`.activeMut`. -/
theorem padded_pinned_loan_blocks_pure_mutation_until_reabsorb_test :
    let initSymVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Init
    let mutSymVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Mut
    let otherSymVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Other
    let st0 := mkSampleU8U32InitState
    let bMutBytes : List AllocByte :=
      (execEncodeUInt execProfileTargetEndian 4 sampleU8U32Mut.bVal.toNat).map
        (fun b => AllocByte.init b none)
    Exists fun stPinned =>
    Exists fun stMut =>
    Exists fun stReabsorbed =>
    Exists fun stWrittenSym =>
    Exists fun stEndSym =>
      freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful st0 =
        .ok stPinned ∧
      writePlaceVal mirValAlg (.derefSub 2 []) otherSymVal
        stPinned.sym = none ∧
      writePlaceVal mirValAlg (.localSub 1 []) otherSymVal
        stPinned.sym = none ∧
      readPlaceVal mirValAlg (.derefSub 2 [])
        stPinned.sym = none ∧
      endLoanInState mirValAlg 0 stPinned.sym = .fail ∧
      mutatePaddedInMem sampleBodyCtx 1 1 4 2 bMutBytes stPinned = .ok stMut ∧
      reabsorbPaddedFromMem sampleBodyCtx 0 stMut =
        .ok stReabsorbed ∧
      readPlaceVal mirValAlg (.localSub 1 []) stReabsorbed.sym =
        none ∧
      readPlaceVal mirValAlg (.derefSub 2 []) stReabsorbed.sym =
        some mutSymVal ∧
      writePlaceVal mirValAlg (.derefSub 2 []) otherSymVal
        stReabsorbed.sym = some stWrittenSym ∧
      endLoanInState mirValAlg 0 stWrittenSym = .ok stEndSym ∧
      getLocal mirValAlg 1 stEndSym = some otherSymVal ∧
      initSymVal ≠ otherSymVal := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  injection hEq with hFields
  injection hFields with hF0 _
  injection hF0 with hSc
  have hBits := congrArg (fun sv : ScalarVal => sv.bits.toNat) hSc
  exact Bool.noConfusion (congrArg (Nat.beq 0x11) hBits)

/-- Negative codec fixture with short `encodeValToMem` output. -/
@[expose] def badShortEncodeCodec : TypedSpatialMemCodec U8U32Struct :=
  { paddedU8U32MemCodec with
    padMask := [false]
    encodeValToMem := fun s => [AllocByte.init s.aByte none] }

/-- Negative codec fixture with short `padMask`. -/
@[expose] def badShortMaskCodec : TypedSpatialMemCodec U8U32Struct :=
  { paddedU8U32MemCodec with
    padMask := [false] }

/-- Negative codec fixture encoding `.uninit` bytes. -/
@[expose] def badFreezeUninitCodec : TypedSpatialMemCodec U8U32Struct :=
  { paddedU8U32MemCodec with
    encodeValToMem := fun _ => List.replicate 8 .uninit }

/-- Negative codec fixture encoding mismatched provenance. -/
@[expose] def badFreezeProvCodec : TypedSpatialMemCodec ProvPtrStruct :=
  { provPtrPaddedMemCodec 7 with
    encodeValToMem := provPtrEncode 99 }

/-- Negative codec fixture forgetting `Val` non-unit tags. -/
@[expose] def unitForgettingCodec : TypedSpatialMemCodec Unit :=
  { codecId := 7
    targetTy := .mirTy .unit
    layout := ⟨0, 0⟩
    padMask := []
    encodeValToMem := fun _ => []
    decodeValFromMem := fun _ => some ()
    provCheck := fun _ => true
    encodeToSymVal := fun _ => .unit
    decodeFromSymVal := fun _ => some () }

/-- Negative codec fixture inverting boolean round-trips. -/
@[expose] def flippingBoolCodec : TypedSpatialMemCodec Bool :=
  { codecId := 8036
    targetTy := .mirTy .bool
    layout := ⟨1, 0⟩
    padMask := [false]
    encodeValToMem := fun b => [.init (if b then 1 else 0) none]
    decodeValFromMem := fun bs =>
      match bs with
      | [.init b _] => some (Nat.beq b.toNat 0)
      | _ => none
    provCheck := fun _ => true
    encodeToSymVal := Val.bool
    decodeFromSymVal := fun v =>
      match v with
      | .bool b => some b
      | _ => none }

/-- Negative codec fixture with mismatched `targetTy`. -/
@[expose] def badWrongTargetTyCodec : TypedSpatialMemCodec Bool :=
  { flippingBoolCodec with
    codecId := 8037
    targetTy := .mirTy (.int .i32 false)
    decodeValFromMem := fun bs =>
      match bs with
      | [.init b _] => some (!Nat.beq b.toNat 0)
      | _ => none }

/-- Negative codec fixture forging pointer provenance. -/
@[expose] def badForgingProvCodec : TypedSpatialMemCodec Unit :=
  { codecId := 8038
    targetTy := .mirTy (.rawPtr .mut (.int .i8 false))
    layout := ⟨8, 3⟩
    padMask := List.replicate 8 false
    encodeValToMem := fun _ => List.replicate 8 (.init 1 none)
    decodeValFromMem := fun _ => some ()
    provCheck := fun _ => true
    encodeToSymVal := fun _ => .ptr ⟨some 77, 0, .isize⟩
    decodeFromSymVal := fun v =>
      if mirValBeqAt 8 v (.ptr ⟨some 77, 0, .isize⟩) then some () else none }

/-- Negative codec fixture attaching provenance to `bool`. -/
@[expose] def badSurplusProvBoolCodec : TypedSpatialMemCodec Bool :=
  { codecId := 8040
    targetTy := .mirTy .bool
    layout := ⟨1, 0⟩
    padMask := [false]
    encodeValToMem := fun b => [.init (if b then 1 else 0) (some 7)]
    decodeValFromMem := fun bs =>
      match bs with
      | [.init b _] => some (!Nat.beq b.toNat 0)
      | _ => none
    provCheck := fun _ => true
    encodeToSymVal := Val.bool
    decodeFromSymVal := fun v =>
      match v with
      | .bool b => some b
      | _ => none }

/-- Negative codec fixture targeting general `MirTy.tuple`. -/
@[expose] def badGeneralTupleCodec : TypedSpatialMemCodec (Bool × Bool) :=
  { codecId := 8041
    targetTy := .mirTy (.tuple [.bool, .bool])
    layout := ⟨2, 0⟩
    padMask := [false, false]
    encodeValToMem := fun p =>
      [.init (if p.1 then 1 else 0) none, .init (if p.2 then 1 else 0) none]
    decodeValFromMem := fun bs =>
      match bs with
      | [.init b1 _, .init b2 _] =>
        some (!Nat.beq b1.toNat 0, !Nat.beq b2.toNat 0)
      | _ => none
    provCheck := fun _ => true
    encodeToSymVal := fun p => .tuple [.bool p.1, .bool p.2]
    decodeFromSymVal := fun v =>
      match v with
      | .tuple [.bool b1, .bool b2] => some (b1, b2)
      | _ => none }

/-- Negative codec fixture targeting unsized pointee pointer. -/
@[expose] def badUnsupPtrCodec : TypedSpatialMemCodec (BitVec 64) :=
  { codecId := 8042
    targetTy := .mirTy (.rawPtr .shared .unsupported)
    layout := ⟨8, 3⟩
    padMask := List.replicate 8 false
    encodeValToMem := fun x =>
      (execEncodeUInt execProfileTargetEndian 8 x.toNat).map
        (fun b => AllocByte.init b none)
    decodeValFromMem := fun _ => some 0
    provCheck := fun _ => true
    encodeToSymVal := fun x => .ptr ⟨none, UInt64.ofNat x.toNat, .isize⟩
    decodeFromSymVal := fun _ => none }

/-- Permissive `provCheck` pointer codec fixture. -/
@[expose] def permissiveProvPtrCodec : TypedSpatialMemCodec ProvPtrStruct :=
  { provPtrPaddedMemCodec 7 with
    codecId := 8039
    provCheck := fun _ => true }

/-- Soundness test fixture `permissiveUninitLawfulDecode`. -/
@[expose] def permissiveUninitLawfulDecode (bs : List AllocByte) :
    Option U8U32Struct :=
  if !nonPadBytesInitialized u8PadU32Mask bs then
    some sampleU8U32Init
  else
    paddedU8U32Decode bs

/-- Soundness test fixture `permissiveUninitLawfulCodec`. -/
@[expose] def permissiveUninitLawfulCodec : TypedSpatialMemCodec U8U32Struct :=
  { paddedU8U32MemCodec with
    codecId := 8035
    decodeValFromMem := permissiveUninitLawfulDecode }

/-- Lawfulness witness for `permissiveUninitLawfulCodec`. -/
theorem permissiveUninitLawfulCodec_lawful :
    LawfulTypedSpatialMemCodec permissiveUninitLawfulCodec := by
  refine ⟨rfl, rfl, ?_, paddedU8U32MemCodec_lawful.2.2.2.1, ?_, ?_, ?_⟩
  · intro x
    have h := paddedU8U32MemCodec_lawful.2.2.1 x
    have hDec : permissiveUninitLawfulDecode (paddedU8U32Encode x) = some x := by
      dsimp only [permissiveUninitLawfulDecode]
      have hNP : nonPadBytesInitialized u8PadU32Mask (paddedU8U32Encode x) = true :=
        h.2.1
      rw [hNP, Bool.not_true, ite_bool_false rfl]
      exact h.2.2.2.2.2.1
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hDec, h.2.2.2.2.2.2⟩
  · intro bs x hLen hNP hProv hDec
    have hNP' : nonPadBytesInitialized u8PadU32Mask bs = true := hNP
    dsimp only [permissiveUninitLawfulCodec, permissiveUninitLawfulDecode] at hDec
    rw [hNP', Bool.not_true, ite_bool_false rfl] at hDec
    exact paddedU8U32MemCodec_lawful.2.2.2.2.1 bs x hLen hNP hProv hDec
  · intro _ _ hTy
    nomatch hTy
  · intro b1 b2 hL1 hL2 hN1 hN2 hSame
    have hN1' : nonPadBytesInitialized u8PadU32Mask b1 = true := hN1
    have hN2' : nonPadBytesInitialized u8PadU32Mask b2 = true := hN2
    have hEq : paddedU8U32Decode b1 = paddedU8U32Decode b2 :=
      paddedU8U32MemCodec_lawful.2.2.2.2.2.2 b1 b2 hL1 hL2 hN1 hN2 hSame
    dsimp only [permissiveUninitLawfulCodec, permissiveUninitLawfulDecode]
    rw [hN1', hN2', Bool.not_true, ite_bool_false rfl, ite_bool_false rfl, hEq]

/-- Byte encoder for `twoValBorrowCodec`. -/
@[expose] def twoValBorrowEncode (b : Bool) : List AllocByte :=
  if b then List.replicate 8 (.init 1 (some 5))
  else List.replicate 8 (.init 0 (some 2))

/-- Byte decoder for `twoValBorrowCodec`. -/
@[expose] def twoValBorrowDecode (bs : List AllocByte) : Option Bool :=
  if allocBytesListBeq bs (List.replicate 8 (.init 1 (some 5))) then
    some true
  else if allocBytesListBeq bs (List.replicate 8 (.init 0 (some 2))) then
    some false
  else
    none

/-- Symbolic encoder for `twoValBorrowCodec`. -/
@[expose] def twoValBorrowToSymVal (b : Bool) : Val :=
  if b then mirEncodeRef 5 [] else mirEncodeRef 2 []

/-- Symbolic decoder for `twoValBorrowCodec`. -/
@[expose] def twoValBorrowFromSymVal : Val → Option Bool
  | .bytes [.init b (some lid)] =>
    if Nat.beq b.toNat 0 && Nat.beq lid 5 then some true
    else if Nat.beq b.toNat 0 && Nat.beq lid 2 then some false
    else none
  | _ => none

/-- Negative codec fixture smuggling borrow handles. -/
@[expose] def twoValBorrowCodec : TypedSpatialMemCodec Bool :=
  { codecId := 8033
    targetTy := .mirTy (.ref .mut .unit)
    layout := ⟨8, 3⟩
    padMask := List.replicate 8 false
    encodeValToMem := twoValBorrowEncode
    decodeValFromMem := twoValBorrowDecode
    provCheck := fun _ => true
    encodeToSymVal := twoValBorrowToSymVal
    decodeFromSymVal := twoValBorrowFromSymVal }

/-- Soundness test fixture `tamperedBorrowInjectingWitness`. -/
@[expose] def tamperedBorrowInjectingWitness : SpatialCodec Val where
  codecId := paddedU8U32MemCodec.codecId
  encode v := (paddedLoanWitnessCodec paddedU8U32MemCodec 1 ⟨1, 0⟩).encode v
  decode cells :=
    match cells with
    | [.init v, .uninit, .init _] => some v
    | [.uninit, .init (.bytes _)] => some (mirEncodeRef 5 [])
    | _ => none
  decode_encode _ := rfl

/-- Soundness test fixture `unitCanonicalZstCodec`. -/
@[expose] def unitCanonicalZstCodec : TypedSpatialMemCodec Unit :=
  { codecId := 8034
    targetTy := .mirTy .unit
    layout := ⟨0, 0⟩
    padMask := []
    encodeValToMem := fun _ => []
    decodeValFromMem := fun bs =>
      match bs with
      | [] => some ()
      | _ :: _ => none
    provCheck := fun _ => true
    encodeToSymVal := fun _ => .unit
    decodeFromSymVal := fun v =>
      match v with
      | .unit => some ()
      | _ => none }

/-- Lawfulness witness for `unitCanonicalZstCodec`. -/
theorem unitCanonicalZstCodec_lawful :
    LawfulTypedSpatialMemCodec unitCanonicalZstCodec := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro v _ hDec
    cases v with
    | unit => rfl
    | scalar _ | ptr _ | bool _ | char _ | ordering _ | enumVal _ _
    | tuple _ | array _ | slicePtr _ _ | vec _ _ _ | boxPtr _ _
    | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | bytes _ =>
      nomatch hDec
  · intro bs _ hLen _ _ _
    cases bs with
    | nil => rfl
    | cons _ _ => nomatch hLen
  · intro ty _ hTy _
    injection hTy with hTyEq
    subst hTyEq
    refine ⟨?_, ?_, ?_⟩
    · intro _
      rw [← execEncodeVal_eq]
      rfl
    · intro _
      rw [← execDecodeVal_eq]
      rfl
    · intro bs _ hLen _ _ _ _
      cases bs with
      | nil =>
        rw [← execDecodeVal_eq]
        rfl
      | cons _ _ => nomatch hLen
  · intro b1 b2 hL1 hL2 _ _ _
    cases b1 with
    | cons _ _ => nomatch hL1
    | nil =>
      cases b2 with
      | cons _ _ => nomatch hL2
      | nil => rfl

/-- Soundness test fixture `pureIdentityCodec`. -/
@[expose] def pureIdentityCodec : SpatialCodec Val :=
  { codecId := 9001
    encode := fun v => [.init v]
    decode := fun cs =>
      match cs with
      | [.init v] => some v
      | _ => none
    decode_encode := fun _ => rfl }

/-- Soundness test fixture `rawBytePtrForgingCodec`. -/
@[expose] def rawBytePtrForgingCodec : SpatialCodec Val :=
  { codecId := 9002
    encode := fun v =>
      match v with
      | .unit => [.rawByte 0]
      | _ => [.init v]
    decode := fun cs =>
      match cs with
      | [.rawByte 0] => some .unit
      | [.rawByte 1] => some (.ptr ⟨some 1, 0, .isize⟩)
      | [.init v] => some v
      | _ => none
    decode_encode := fun v => by
      cases v <;> rfl }

/-- Negative `#[repr(C)]` bool codec accepting byte `2`. -/
@[expose] def badLenientReprCBoolCodec : TypedSpatialMemCodec Bool where
  codecId := 8042
  targetTy := .reprCAdt 8042 [⟨0, .bool⟩]
  layout := ⟨1, 0⟩
  padMask := [false]
  encodeValToMem := fun b => [AllocByte.init (if b then 1 else 0) none]
  decodeValFromMem := fun bs =>
    match bs with
    | [.init b none] => some (!Nat.beq b.toNat 0)
    | _ => none
  provCheck := fun _ => true
  encodeToSymVal := fun b => .tuple [.bool b]
  decodeFromSymVal := fun v =>
    match v with
    | .tuple [.bool b] => some b
    | _ => none

/-- Negative pointer codec rewriting decoded offsets. -/
@[expose] def badLenientPtrOffsetCodec : TypedSpatialMemCodec ProvPtrStruct :=
  { provPtrPaddedMemCodec 7 with
    codecId := 8043
    decodeValFromMem := fun bs =>
      match provPtrDecode bs with
      | none => none
      | some s => some ⟨s.tagByte, BitVec.ofNat 64 0x2000⟩ }

/-- Verifies that round-trip-inverting (`flippingBoolCodec`), short-encoding,
short-mask, uninitialized-encoding, wrong-provenance, value-forgetting,
mismatched-`targetTy`, provenance-forging, surplus-provenance-injecting
(`badSurplusProvBoolCodec`), borrow-handle (`twoValBorrowCodec`), general-tuple
(`badGeneralTupleCodec`), unsized-pointee-pointer (`badUnsupPtrCodec`),
lenient-`#[repr(C)]`-bool (`badLenientReprCBoolCodec`), and
offset-rewriting-pointer (`badLenientPtrOffsetCodec`) codecs are all refuted by
`LawfulTypedSpatialMemCodec` (so they cannot be passed to `freezePaddedToMem`),
and that `paddedLoanWitnessCodec` also enforces per-field byte-value and
bidirectional provenance conservation at runtime (blocking provenance
stripping, forgery, cross-field laundering onto `u8`, padding provenance
smuggling, invalid `bool` byte `2`, and wrong decoded pointer offsets) even when
`codec.provCheck := fun _ => true`. -/
theorem unlawful_codecs_and_codec_independent_provenance_tests :
    ¬ LawfulTypedSpatialMemCodec flippingBoolCodec ∧
    ¬ LawfulTypedSpatialMemCodec badShortEncodeCodec ∧
    ¬ LawfulTypedSpatialMemCodec badShortMaskCodec ∧
    ¬ LawfulTypedSpatialMemCodec badFreezeUninitCodec ∧
    ¬ LawfulTypedSpatialMemCodec badFreezeProvCodec ∧
    ¬ LawfulTypedSpatialMemCodec unitForgettingCodec ∧
    ¬ LawfulTypedSpatialMemCodec badWrongTargetTyCodec ∧
    ¬ LawfulTypedSpatialMemCodec badForgingProvCodec ∧
    ¬ LawfulTypedSpatialMemCodec badSurplusProvBoolCodec ∧
    ¬ LawfulTypedSpatialMemCodec twoValBorrowCodec ∧
    ¬ LawfulTypedSpatialMemCodec badGeneralTupleCodec ∧
    ¬ LawfulTypedSpatialMemCodec badUnsupPtrCodec ∧
    ¬ LawfulTypedSpatialMemCodec badLenientReprCBoolCodec ∧
    ¬ LawfulTypedSpatialMemCodec badLenientPtrOffsetCodec ∧
    (paddedLoanWitnessCodec permissiveProvPtrCodec 1 ⟨1, 0⟩).decode
      [.uninit,
       .init (.bytes (provPtrEncode 7 ⟨0x10, BitVec.ofNat 64 0x1000⟩))] =
      some ((provPtrPaddedMemCodec 7).encodeToSymVal ⟨0x10, BitVec.ofNat 64 0x1000⟩) ∧
    (paddedLoanWitnessCodec permissiveProvPtrCodec 1 ⟨1, 0⟩).decode
      [.uninit,
       .init (.bytes
         ([AllocByte.init 0x10 none, .uninit, .uninit, .uninit,
           .uninit, .uninit, .uninit, .uninit, .init 0 none] ++
          List.replicate 7 (.init 0 (some 7))))] = none ∧
    (paddedLoanWitnessCodec permissiveProvPtrCodec 1 ⟨1, 0⟩).decode
      [.uninit,
       .init (.bytes
         ([AllocByte.init 0x10 none, .uninit, .uninit, .uninit,
           .uninit, .uninit, .uninit, .uninit, .init 0 (some 99)] ++
          List.replicate 7 (.init 0 (some 7))))] = none ∧
    (paddedLoanWitnessCodec permissiveProvPtrCodec 1 ⟨1, 0⟩).decode
      [.uninit,
       .init (.bytes
         ([AllocByte.init 0x10 (some 7), .uninit, .uninit, .uninit,
           .uninit, .uninit, .uninit, .uninit] ++
          (execEncodeUInt execProfileTargetEndian 8 0x1000).map
            (fun b => AllocByte.init b (some 7))))] = none ∧
    (paddedLoanWitnessCodec permissiveProvPtrCodec 1 ⟨1, 0⟩).decode
      [.uninit,
       .init (.bytes
         ([AllocByte.init 0x10 none, .init 0 (some 7), .uninit, .uninit,
           .uninit, .uninit, .uninit, .uninit] ++
          (execEncodeUInt execProfileTargetEndian 8 0x1000).map
            (fun b => AllocByte.init b (some 7))))] = none ∧
    (paddedLoanWitnessCodec badLenientReprCBoolCodec 1 ⟨1, 0⟩).decode
      [.uninit, .init (.bytes [AllocByte.init 2 none])] = none ∧
    (paddedLoanWitnessCodec badLenientPtrOffsetCodec 1 ⟨1, 0⟩).decode
      [.uninit,
       .init (.bytes (provPtrEncode 7 ⟨0x10, BitVec.ofNat 64 0x1000⟩))] =
        none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    have hRT := (h.2.2.1 false).2.2.2.2.2.1
    change some true = some false at hRT
    nomatch hRT
  · intro h
    have hLen := (h.2.2.1 sampleU8U32Init).1
    change 1 = 8 at hLen
    nomatch hLen
  · intro h
    have hLen := h.2.1
    change 1 = 8 at hLen
    nomatch hLen
  · intro h
    have hNP := (h.2.2.1 sampleU8U32Init).2.1
    change false = true at hNP
    nomatch hNP
  · intro h
    have hPr := (h.2.2.1 ⟨0x10, BitVec.ofNat 64 0x1000⟩).2.2.1
    change false = true at hPr
    nomatch hPr
  · intro h
    have hInj := h.2.2.2.1 (.bool true) () rfl
    nomatch hInj
  · intro h
    nomatch h.1
  · intro h
    have hPS := (h.2.2.1 ()).2.2.2.2.1
    change false = true at hPS
    nomatch hPS
  · intro h
    have hSP := (h.2.2.1 true).2.2.2.2.1
    change false = true at hSP
    nomatch hSP
  · intro h
    nomatch h.1
  · intro h
    nomatch h.1
  · intro h
    nomatch h.1
  · intro h
    have hGetPut := h.2.2.2.2.1 [AllocByte.init 2 none] true rfl rfl rfl rfl
    change false = true at hGetPut
    nomatch hGetPut
  · intro h
    have hGetPut :=
      h.2.2.2.2.1 (provPtrEncode 7 ⟨0x10, BitVec.ofNat 64 0x1000⟩)
        ⟨0x10, BitVec.ofNat 64 0x2000⟩ rfl rfl rfl rfl
    change false = true at hGetPut
    nomatch hGetPut

/-- Negative guard and lifecycle regression suite exercising fail-closed guards
across `freezePaddedToMem`, `mutatePaddedInMem`, `reabsorbPaddedFromMem`,
`reusablePromotedPlace`, and `deallocatePromotedLocal`, including duplicate
`LoanId`s, non-root-local targets, `decodeFromSymVal = none`, lawful
permissive-decoder `.uninit` rejection, isolated codec/owner/`MemPlace`/
`LayoutData`/`loanBid` witness tampering (backed by live in-bounds aligned
memory at `⟨99, 0⟩` and `⟨1, 4⟩`), cross-layer `st.sym.spatial` collision and
`reabsorbFromSpatialInState` blocking, lawful 2-valued distinct-active-loan
borrow-handle injection, out-of-bounds and misaligned zero-length writes,
return-place `_0` protection, conservative `LoanId` vs. `AllocId` handle
collision (`valFreeOfAllocId`), live `.spatialPinned` decoders and `.rawByte`
cells, escaped pointers across symbolic and memory reservoirs, and both
negative and positive in-place reuse of a promoted `LocalSlot.indirect`
allocation. -/
theorem padded_spatial_negative_guards_tests :
    let st0 := mkSampleU8U32InitState
    let initVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Init
    let otherVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Other
    let ptrTo1 : Val := .ptr ⟨some 1, 0, .isize⟩
    let memTamperBacking : MemoryState :=
      { nextAllocId := 100
        allocations :=
          [⟨1, 2, .mut,
             List.replicate 4 (.init 0 none) ++
               paddedU8U32Encode sampleU8U32Init ++
               List.replicate 4 (.init 0 none),
             true⟩,
           ⟨99, 2, .mut, paddedU8U32Encode sampleU8U32Init, true⟩] }
    -- 1. Pure loan-graph guards on `freezePaddedToMem`: duplicate `LoanId`,
    --    non-activeMut, borrowed, active child loan/region, non-root target,
    --    `decodeFromSymVal = none`, and block-table collisions.
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := [⟨0, .activeMut, ⟨initVal, .unborrowed⟩, .direct (.localReg 1) []⟩,
                    ⟨0, .ended, ⟨initVal, .unborrowed⟩, .direct (.localReg 1) []⟩] } } =
        .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := [⟨0, .ended, ⟨initVal, .unborrowed⟩, .direct (.localReg 1) []⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := [⟨0, .activeMut, ⟨initVal, .shared [1]⟩, .direct (.localReg 1) []⟩] } } =
        .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := [⟨0, .activeMut, ⟨initVal, .unborrowed⟩, .direct (.localReg 1) []⟩,
                    ⟨1, .activeShared, ⟨initVal, .unborrowed⟩, .direct (.parentLoan 0) []⟩] } } =
        .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          regionGroups :=
            [⟨0, true, 0, [(.parentLoan 0, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := [⟨0, .activeMut, ⟨initVal, .unborrowed⟩, .direct (.localReg 1) [0]⟩] } } =
        .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := [⟨0, .activeMut, ⟨initVal, .unborrowed⟩, .rootParam 0⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨.unit, .mutLocked 0⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩]
          loans := [⟨0, .activeMut, ⟨.unit, .unborrowed⟩, .direct (.localReg 1) []⟩] }
        mirLocals := [.immediate (some .unit), .immediate (some .unit),
                      .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        memBlocks := [⟨9, 0, 1, .readWrite, 9, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        memBlocks := [⟨1, 9, 1, .readWrite, 1, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          spatial := [⟨9, 0, .readWrite, 9, 0, [.init .unit]⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          spatial := [⟨1, 9, .readWrite, 1, 0, [.init .unit]⟩] } } = .fail ∧
    -- 2. Dead, uninitialized, or mismatched immediate MIR locals fail closed.
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocals := [.immediate (some .unit), .dead,
                      .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocals := [.immediate (some .unit), .immediate none,
                      .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocals := [.immediate (some .unit), .immediate (some otherVal),
                      .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
    -- 3. Lawful permissive decoder still fails closed on `.uninit` non-padding
    --    byte.
    (match freezePaddedToMem sampleBodyCtx 0 permissiveUninitLawfulCodec
        permissiveUninitLawfulCodec_lawful st0 with
     | .fail => False
     | .ok stPermPinned =>
       match execWriteUninit stPermPinned.mem ⟨1, 0⟩ 1 0 with
       | .error _ => False
       | .ok memUninit0 =>
         reabsorbPaddedFromMem sampleBodyCtx 0 { stPermPinned with mem := memUninit0 } = .fail) ∧
    -- 4. Defense-in-depth `replaceableVal` guard on `reabsorbPaddedFromMem`:
    --    even if a tampered `.spatialPinned` witness matches the block's
    --    `encode` sentinel while decoding to an active sibling borrow handle
    --    (`mirEncodeRef 5 []` absent from initial `initVal`),
    --    `reabsorbPaddedFromMem` rejects it via `replaceableVal`.
    (match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful st0 with
     | .fail => False
     | .ok stInjPinned =>
       let stInjTampered : PaddedSymMemState :=
         { stInjPinned with
           sym :=
             { stInjPinned.sym with
               locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .mutLocked 0⟩,
                          ⟨.unit, .mutLocked 5⟩]
               loans :=
                 [⟨0, .spatialPinned 1 tamperedBorrowInjectingWitness,
                   ⟨initVal, .unborrowed⟩, .direct (.localReg 1) []⟩,
                  ⟨5, .activeMut, ⟨.unit, .unborrowed⟩,
                   .direct (.localReg 2) []⟩] }
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩,
                         .immediate (some .unit)] }
       reabsorbPaddedFromMem sampleBodyCtx 0 stInjTampered = .fail) ∧
    -- 5. Conservative `LoanId` / `AllocId` handle over-approximation check.
    valFreeOfAllocId 8 1 (mirEncodeRef 1 []) = false ∧
    valFreeOfAllocId 8 1 (mirEncodeRef 0 []) = true ∧
    -- 6. Witness authentication (`codecId`, `ownerLocal`, `wOwner`, `wAlloc`,
    --    `wOff`, `layout`, `loanBid`), duplicate `LoanId`, pure-reabsorb
    --    blocking, reuse, and escape-reservoir deallocation guards.
    (match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful st0 with
     | .fail => False
     | .ok stPinned =>
       let witness1 := paddedLoanWitnessCodec paddedU8U32MemCodec 1 ⟨1, 0⟩
       let witnessOwner2 := paddedLoanWitnessCodec paddedU8U32MemCodec 2 ⟨1, 0⟩
       mutatePaddedInMem sampleBodyCtx 1 1 9 0 [] stPinned = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 3 [] stPinned = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           sym := { stPinned.sym with
             loans := stPinned.sym.loans ++ stPinned.sym.loans } } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             loans := stPinned.sym.loans ++ stPinned.sym.loans } } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           sym := { stPinned.sym with
             loans := [⟨0, .spatialPinned 99 witness1, ⟨initVal, .unborrowed⟩,
                        .direct (.localReg 1) []⟩] } } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           sym := { stPinned.sym with
             loans := [⟨0, .spatialPinned 1 witnessOwner2, ⟨initVal, .unborrowed⟩,
                        .direct (.localReg 1) []⟩] } } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             loans := [⟨0, .spatialPinned 1 witnessOwner2, ⟨initVal, .unborrowed⟩,
                        .direct (.localReg 1) []⟩] } } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           mirLocals := [.immediate (some .unit), .immediate none, .immediate none] } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with codecId := 9999 }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with codecId := 9999 }) } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨99, 0⟩, .immediate none]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨99, 0⟩ }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨99, 0⟩, .immediate none]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨99, 0⟩ }) } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩, .immediate none]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨1, 4⟩ }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩, .immediate none]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨1, 4⟩ }) } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 [.init 1 none]
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with layout := ⟨4, 2⟩ }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with layout := ⟨4, 2⟩ }) } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 [.init 1 none]
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with layout := ⟨8, 1⟩ }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with layout := ⟨8, 1⟩ }) } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with perm := .readOnly }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with perm := .readOnly }) } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with activeSubSplits := 1 }) } =
           .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with activeSubSplits := 1 }) } =
           .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks ++
             [⟨2, 0, 1, .readWrite, 2, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             spatial := [⟨99, 0, .readWrite, 99, 0, []⟩] } } = .fail ∧
       reabsorbFromSpatialInState mirValAlg 0 witness1
         { stPinned.sym with
           spatial := [⟨1, 0, .readWrite, 1, 0, [.rawByte 1, .init .unit]⟩] } = .fail ∧
       reabsorbFromSpatialInState mirValAlg 0 witness1
         { stPinned.sym with
           spatial := [⟨1, 0, .readWrite, 1, 0, witness1.encode initVal⟩] } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
         { stPinned with
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩, .indirect ⟨1, 0⟩]
           memBlocks := stPinned.memBlocks.map (fun b => { b with ownerLocal := 2 }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩, .indirect ⟨1, 0⟩]
           memBlocks := stPinned.memBlocks.map (fun b => { b with ownerLocal := 2 }) } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with mirLocals := [.immediate (some .unit), .dead, .immediate none] } = .fail ∧
       deallocatePromotedLocal sampleBodyCtx 1 stPinned = .fail ∧
       (match reabsorbPaddedFromMem sampleBodyCtx 0 stPinned with
        | .fail => False
        | .ok stReab =>
          stReab.mirLocals =
            [.immediate (some .unit), .indirect ⟨1, 0⟩,
             .immediate (some (mirEncodeRef 0 []))] ∧
          (match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful stReab with
           | .fail => False
           | .ok stRefrozen => stRefrozen.mem.nextAllocId = stReab.mem.nextAllocId) ∧
          -- Positive in-place reuse preserves existing `0xAA` padding bytes:
          (match execWriteBytes stReab.mem ⟨1, 1⟩ 0
               [.init 0xAA none, .init 0xAA none, .init 0xAA none] with
           | .error _ => False
           | .ok memPadAA =>
             match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec
                 paddedU8U32MemCodec_lawful { stReab with mem := memPadAA } with
             | .fail => False
             | .ok stRefrozenAA =>
               execReadBytes stRefrozenAA.mem ⟨1, 1⟩ 3 0 =
                 .ok [.init 0xAA none, .init 0xAA none, .init 0xAA none]) ∧
          -- Negative in-place reuse (`PromotedLocalEntry`,
          -- `reusablePromotedPlace`, and initialized/synchronized memory):
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mem := { stReab.mem with
                allocations := [⟨1, 2, .mut, List.replicate 8 .uninit, true⟩] } } =
            .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mem := { stReab.mem with
                allocations := [⟨1, 2, .mut, paddedU8U32Encode sampleU8U32Other, true⟩] } } =
            .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with promotedLocals := [] } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              promotedLocals := stReab.promotedLocals.map
                (fun e => { e with localTy := .mirTy .unit }) } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩,
                            .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩,
                            .immediate (some ptrTo1)] } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                locals := [⟨.unit, .unborrowed⟩, ⟨ptrTo1, .mutLocked 0⟩,
                           ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .mutLocked 0⟩,
                           ⟨ptrTo1, .unborrowed⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                loans := stReab.sym.loans ++
                  [⟨2, .activeMut, ⟨ptrTo1, .unborrowed⟩, .direct (.localReg 2) []⟩] } } =
            .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                loans := stReab.sym.loans ++
                  [⟨2, .spatialPinned 5 rawBytePtrForgingCodec, ⟨.unit, .unborrowed⟩,
                     .direct (.localReg 2) []⟩] } } =
            .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                spatial := [⟨5, 2, .readWrite, 5, 0, [.init ptrTo1]⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                spatial := [⟨5, 2, .readWrite, 5, 0, [.rawByte 1]⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                regionDeposits := [(0, ptrTo1)] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              sym := { stReab.sym with
                regionGroups :=
                  [⟨0, true, 2, [(.localReg 2, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mem := { stReab.mem with
                allocations := stReab.mem.allocations ++
                  [⟨2, 3, .mut, [.init 0 (some 1)], true⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              memBlocks := [⟨5, 2, 2, .readWrite, 5, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mem := { stReab.mem with
                allocations := [⟨1, 2, .shared, paddedU8U32Encode sampleU8U32Init, true⟩] } } =
            .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mem := { stReab.mem with
                allocations := [⟨1, 2, .mut, [.uninit], true⟩] } } = .fail ∧
          freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
            { stReab with
              mem := { stReab.mem with
                allocations := [⟨1, 1, .mut, paddedU8U32Encode sampleU8U32Init, true⟩] } } =
            .fail ∧
          (match endLoanInState mirValAlg 0 stReab.sym with
           | .fail => False
           | .ok symEnded =>
             deallocatePromotedLocal sampleBodyCtx 0
               { stReab with
                 sym := symEnded
                 mirLocals := [.indirect ⟨1, 0⟩, .immediate (some initVal),
                               .immediate (some .unit)] } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := symEnded
                 mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩,
                               .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := symEnded
                 mirLocals := [.immediate (some .unit), .immediate (some initVal),
                               .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .shared [9]⟩,
                              ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := symEnded
                 memBlocks := [⟨5, 2, 2, .readWrite, 5, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := symEnded
                 promotedLocals := stReab.promotedLocals ++
                   [⟨2, paddedU8U32MemCodec.targetTy, ⟨1, 0⟩, ⟨8, 2⟩,
                     u8PadU32Mask, 8032, encodeSymOfCodec paddedU8U32MemCodec⟩] } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := symEnded
                 mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩,
                               .immediate (some ptrTo1)] } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩,
                              ⟨ptrTo1, .unborrowed⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩,
                              ⟨mirEncodeRef 1 [], .unborrowed⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   loans := symEnded.loans ++
                     [⟨2, .activeMut, ⟨ptrTo1, .unborrowed⟩, .direct (.localReg 2) []⟩] } } =
               .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   loans := symEnded.loans ++
                     [⟨2, .activeMut, ⟨.unit, .unborrowed⟩,
                       .choice ptrTo1 (.direct (.localReg 2) []) (.direct (.localReg 2) [])⟩] } } =
               .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   loans := symEnded.loans ++
                     [⟨2, .activeMut, ⟨.unit, .unborrowed⟩,
                       .choice (.bool true) (.direct (.localReg 1) [])
                         (.direct (.localReg 2) [])⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   loans := symEnded.loans ++
                     [⟨2, .activeMut, ⟨.unit, .unborrowed⟩,
                       .lensCall [(.localReg 2, [])] (fun v => some [v])⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   loans := symEnded.loans ++
                     [⟨2, .activeMut, ⟨.unit, .unborrowed⟩,
                       .lensCall [(.localReg 1, [])] (fun v => some [v])⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   regionDeposits := [(0, ptrTo1)] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   regionGroups :=
                     [⟨0, true, 2, [(.localReg 2, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := symEnded
                 mem := { stReab.mem with
                   allocations := stReab.mem.allocations ++
                     [⟨2, 3, .mut, [.init 0 (some 1)], true⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   loans := symEnded.loans ++
                     [⟨2, .spatialPinned 5 rawBytePtrForgingCodec, ⟨.unit, .unborrowed⟩,
                        .direct (.localReg 2) []⟩] } } = .fail ∧
             deallocatePromotedLocal sampleBodyCtx 1
               { stReab with
                 sym := { symEnded with
                   spatial := [⟨5, 2, .readWrite, 5, 0, [.rawByte 1]⟩] } } = .fail ∧
             (let symWithLoan2 : SymState Val :=
                { symEnded with
                  locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩, ⟨.unit, .mutLocked 2⟩]
                  loans := symEnded.loans ++
                    [⟨2, .activeMut, ⟨.unit, .unborrowed⟩, .direct (.localReg 2) []⟩] }
              match freezeToSpatialInState mirValAlg 2 pureIdentityCodec symWithLoan2 with
              | .fail => False
              | .ok symPurePinned =>
                match mutateSpatialInState 2 2 [.init ptrTo1] symPurePinned with
                | .fail => False
                | .ok symPureEscaped =>
                  deallocatePromotedLocal sampleBodyCtx 1 { stReab with sym := symPureEscaped } = .fail) ∧
             (let symWithRawLoan2 : SymState Val :=
                { symEnded with
                  locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩, ⟨.unit, .mutLocked 2⟩]
                  loans := symEnded.loans ++
                    [⟨2, .activeMut, ⟨.unit, .unborrowed⟩, .direct (.localReg 2) []⟩] }
              match freezeToSpatialInState mirValAlg 2 rawBytePtrForgingCodec symWithRawLoan2 with
              | .fail => False
              | .ok symRawPinned =>
                match mutateSpatialInState 2 2 [.rawByte 1] symRawPinned with
                | .fail => False
                | .ok symRawMut =>
                  deallocatePromotedLocal sampleBodyCtx 1 { stReab with sym := symRawMut } = .fail ∧
                  freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
                    { stReab with sym := { stReab.sym with
                        loans := stReab.sym.loans ++ symRawMut.loans.drop 1
                        spatial := symRawMut.spatial } } = .fail) ∧
             (match deallocatePromotedLocal sampleBodyCtx 1
                { stReab with
                  sym := symEnded
                  mem := { stReab.mem with
                    allocations := stReab.mem.allocations ++
                      [⟨2, 3, .mut, [.init 0 (some 1)], false⟩] } } with
              | .fail => False
              | .ok stDead =>
                stDead.mirLocals =
                  [.immediate (some .unit), .dead,
                   .immediate (some (mirEncodeRef 0 []))] ∧
                stDead.promotedLocals = [] ∧
                getLocal mirValAlg 1 stDead.sym = some .unit)))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl,
   rfl, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl,
    ⟨rfl, rfl,
     rfl, rfl, rfl,
     rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     ⟨rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩,
      ⟨rfl, rfl, rfl⟩⟩⟩⟩⟩

/-- Verifies owner-local lock coherence (`ownerLocalExclusivelyHeldByLoan`),
`mirLocalTypes` binding, `freshPromotedAllocId` reservoir and opaque-decoder
checks on `.immediate` promotion, pinned symbolic coherence
(`pinnedLoanSymCoherent`), zero-length write alignment, and live mutable slice
validation (`liveMutSliceValid`). -/
theorem padded_owner_lock_and_slice_coherence_negative_tests :
    let st0 := mkSampleU8U32InitState
    let initVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Init
    let ptrTo1 : Val := .ptr ⟨some 1, 0, .isize⟩
    -- 1. `freezePaddedToMem` rejects `mirLocalTypes` length or type mismatch.
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with mirLocalTypes := [.mirTy .unit] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocalTypes :=
          [.mirTy .unit, .mirTy (.int .i32 false),
           .mirTy (.ref .mut paddedU8U32MemCodec.targetTy.toCapturedMirTy)] } = .fail ∧
    freezePaddedToMem u32SyncCtx 0 unitCanonicalZstCodec unitCanonicalZstCodec_lawful
      { st0 with
        mirLocalTypes :=
          [.mirTy .unit, .mirTy (.int .i32 false),
           .mirTy (.ref .mut (.int .i32 false))] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 u32MemCodec u32MemCodec_lawful st0 = .fail ∧
    -- 2. `freezePaddedToMem` rejects non-exclusive or missing lock on `reg`.
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .shared [0]⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .mutLocked 99⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .mutJoined [0, 99] []⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩,
                     ⟨initVal, .split [([], .mutLocked 0), ([0], .shared [99])]⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .split [([0], .mutLocked 0)]⟩,
                     ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with sym := { st0.sym with locals := [⟨.unit, .unborrowed⟩] } } = .fail ∧
    -- 3. Sibling loans or active region groups mentioning `reg` fail closed.
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := st0.sym.loans ++
            [⟨2, .activeMut, ⟨initVal, .unborrowed⟩, .direct (.localReg 1) []⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := st0.sym.loans ++
            [⟨2, .activeMut, ⟨initVal, .unborrowed⟩,
               .lensCall [(.localReg 1, [])] (fun v => some [v])⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          regionGroups :=
            [⟨0, true, 2, [(.localReg 1, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
    -- 4. Pre-existing `nextAllocId` references across all reservoirs and opaque
    --    decoders fail closed on `.immediate` promotion (`nextAllocId = 1`),
    --    while advancing `nextAllocId` to `2` succeeds.
    freezePaddedToMem (provBodyCtx 1) 0 (provPtrPaddedMemCodec 1) (provPtrPaddedMemCodec_lawful 1)
      (mkProvInitState 1) = .fail ∧
    (match freezePaddedToMem (provBodyCtx 1) 0 (provPtrPaddedMemCodec 1)
        (provPtrPaddedMemCodec_lawful 1)
        { mkProvInitState 1 with mem := ⟨2, []⟩ } with
     | .ok stOk => stOk.mem.nextAllocId = 3
     | .fail => False) ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mem := ⟨1, [⟨1, 2, .mut, paddedU8U32Encode sampleU8U32Init, true⟩]⟩ } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mem := ⟨1, [⟨2, 3, .mut, [.init 0 (some 1)], false⟩]⟩ } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        memBlocks := [⟨9, 2, 2, .readWrite, 9, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        promotedLocals :=
          [⟨2, paddedU8U32MemCodec.targetTy, ⟨1, 0⟩, ⟨8, 2⟩,
            u8PadU32Mask, 8032, encodeSymOfCodec paddedU8U32MemCodec⟩] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocals := [.immediate (some .unit), .immediate (some initVal),
                      .indirect ⟨1, 0⟩] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocals := [.immediate (some .unit), .immediate (some initVal),
                      .immediate (some ptrTo1)] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        mirLocals := [.immediate (some .unit), .immediate (some initVal),
                      .immediate (some (mirEncodeRef 1 []))] } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .mutLocked 0⟩,
                     ⟨ptrTo1, .unborrowed⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := st0.sym.loans ++
            [⟨2, .activeMut, ⟨ptrTo1, .unborrowed⟩, .direct (.localReg 2) []⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          loans := st0.sym.loans ++
            [⟨2, .spatialPinned 5 rawBytePtrForgingCodec, ⟨.unit, .unborrowed⟩,
               .direct (.localReg 2) []⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          spatial := [⟨5, 2, .readWrite, 5, 0, [.init ptrTo1]⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          spatial := [⟨5, 2, .readWrite, 5, 0, [.rawByte 1]⟩] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with regionDeposits := [(0, ptrTo1)] } } = .fail ∧
    freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful
      { st0 with
        sym := { st0.sym with
          regionGroups :=
            [⟨0, true, 2, [(.localReg 2, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
    -- 5. `mutatePaddedInMem` and `reabsorbPaddedFromMem` enforce symbolic lock
    --    coherence, zero-length alignment, and live `.mut` backing allocations.
    (match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful st0 with
     | .fail => False
     | .ok stPinned =>
       let witness1 := paddedLoanWitnessCodec paddedU8U32MemCodec 1 ⟨1, 0⟩
       let deadMem : MemoryState :=
         ⟨2, [⟨1, 2, .mut, paddedU8U32Encode sampleU8U32Init, false⟩]⟩
       let sharedMem : MemoryState :=
         ⟨2, [⟨1, 2, .shared, paddedU8U32Encode sampleU8U32Init, true⟩]⟩
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 []
         { stPinned with
           sym := { stPinned.sym with
             locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩,
                        ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩,
                        ⟨mirEncodeRef 0 [], .unborrowed⟩] } } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 []
         { stPinned with
           sym := { stPinned.sym with
             loans := [⟨0, .spatialPinned 1 witness1, ⟨initVal, .shared [9]⟩,
                        .direct (.localReg 1) []⟩] } } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             loans := [⟨0, .spatialPinned 1 witness1, ⟨initVal, .shared [9]⟩,
                        .direct (.localReg 1) []⟩] } } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 []
         { stPinned with
           sym := { stPinned.sym with
             loans := stPinned.sym.loans ++
               [⟨2, .activeShared, ⟨initVal, .unborrowed⟩, .direct (.parentLoan 0) []⟩] } } =
         .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             loans := stPinned.sym.loans ++
               [⟨2, .activeShared, ⟨initVal, .unborrowed⟩, .direct (.parentLoan 0) []⟩] } } =
         .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 []
         { stPinned with
           sym := { stPinned.sym with
             regionGroups :=
               [⟨0, true, 2, [(.localReg 1, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           sym := { stPinned.sym with
             regionGroups :=
               [⟨0, true, 2, [(.localReg 1, [])], [], [], fun _ _ => none⟩] } } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 1 2 [] stPinned = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 [] { stPinned with mem := deadMem } = .fail ∧
       mutatePaddedInMem sampleBodyCtx 1 1 0 0 [] { stPinned with mem := sharedMem } = .fail) ∧
    -- 6. ZST reabsorption also fails closed on dead or `.shared` allocations.
    (let stZst0 : PaddedSymMemState :=
       { sym :=
           { locals := [⟨.unit, .unborrowed⟩, ⟨.unit, .mutLocked 0⟩]
             loans := [⟨0, .activeMut, ⟨.unit, .unborrowed⟩, .direct (.localReg 1) []⟩]
             regionGroups := []
             regionDeposits := []
             spatial := []
             nextSpatialTag := 1 }
         mirLocalTypes := [.mirTy .unit, .mirTy .unit]
         mirLocals := [.immediate (some .unit), .immediate (some .unit)]
         mem := execMemoryEmpty
         memBlocks := []
         promotedLocals := [] }
     match freezePaddedToMem zstBodyCtx 0 unitCanonicalZstCodec unitCanonicalZstCodec_lawful
         stZst0 with
     | .fail => False
     | .ok stZstPinned =>
       reabsorbPaddedFromMem zstBodyCtx 0
         { stZstPinned with mem := ⟨2, [⟨1, 0, .mut, [], false⟩]⟩ } = .fail ∧
       reabsorbPaddedFromMem zstBodyCtx 0
         { stZstPinned with mem := ⟨2, [⟨1, 0, .shared, [], true⟩]⟩ } = .fail) :=
  ⟨rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, rfl⟩⟩

/-- Verifies promoted-local authority and synchronization across `u32MemCodec`:
(a) freezing, mutating in `MemoryState` (`10 -> 20`), and reabsorbing keeps
`allPromotedLocalsMemSynced = true` and `evalPaddedMirOperand` reading `20`;
(b) unsynchronized direct `writePlaceVal` (`20 -> 30`) or untracked
`LocalSlot.indirect` flips `allPromotedLocalsMemSynced` to `false` and causes
`evalPaddedMirOperand` to reject stale MIR reads with `.error .unsupported`; and
(c) `writePaddedSymPlace` and `endPaddedLoan` refresh `st.mem`, keep
`allPromotedLocalsMemSynced = true`, make `evalPaddedMirOperand` read `30` then
`40` (matching `Trusted.MirSemantics.evalPrimitiveOperand`), and reject
`Operand.move` out of promoted locals with `.error .unsupported` until
`deallocatePromotedLocal`. -/
theorem promoted_u32_sync_and_stale_mir_read_rejected_test :
    let v10 := u32MemToSymVal (BitVec.ofNat 32 10)
    let v20 := u32MemToSymVal (BitVec.ofNat 32 20)
    let v30 := u32MemToSymVal (BitVec.ofNat 32 30)
    let v40 := u32MemToSymVal (BitVec.ofNat 32 40)
    let mirTys : List SpatialTargetSpec :=
      [.mirTy .unit, .mirTy (.int .i32 false),
       .mirTy (.ref .mut (.int .i32 false))]
    let mirLocsInd : List LocalSlot :=
      [.immediate (some .unit), .indirect ⟨1, 0⟩,
       .immediate (some (mirEncodeRef 0 []))]
    let entry1 : PromotedLocalEntry :=
      ⟨1, .mirTy (.int .i32 false), ⟨1, 0⟩, ⟨4, 2⟩, [false, false, false, false],
       4032, encodeSymOfCodec u32MemCodec⟩
    let witness1 := paddedLoanWitnessCodec u32MemCodec 1 ⟨1, 0⟩
    let blk1 : PaddedSpatialBlock :=
      ⟨1, 0, 1, .readWrite, 1, 0, ⟨4, 2⟩, ⟨1, 0⟩, 4032⟩
    let memOf (x : Nat) (live : Bool) : MemoryState :=
      ⟨2, [⟨1, 2, .mut, u32MemEncode (BitVec.ofNat 32 x), live⟩]⟩
    let st0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.unit, .unborrowed⟩, ⟨v10, .mutLocked 0⟩,
                       ⟨mirEncodeRef 0 [], .unborrowed⟩]
            loans := [⟨0, .activeMut, ⟨v10, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := mirTys
        mirLocals := [.immediate (some .unit), .immediate (some v10),
                      .immediate (some (mirEncodeRef 0 []))]
        mem := execMemoryEmpty
        memBlocks := []
        promotedLocals := [] }
    let stPinned : PaddedSymMemState :=
      { sym :=
          { st0.sym with
            loans := [⟨0, .spatialPinned 1 witness1, ⟨v10, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            nextSpatialTag := 2 }
        mirLocalTypes := mirTys
        mirLocals := mirLocsInd
        mem := memOf 10 true
        memBlocks := [blk1]
        promotedLocals := [entry1] }
    let stMut20 : PaddedSymMemState :=
      { stPinned with mem := memOf 20 true }
    let stReab20 : PaddedSymMemState :=
      { sym :=
          { st0.sym with
            loans := [⟨0, .activeMut, ⟨v20, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            nextSpatialTag := 2 }
        mirLocalTypes := mirTys
        mirLocals := mirLocsInd
        mem := memOf 20 true
        memBlocks := []
        promotedLocals := [entry1] }
    let symUnsynced30 : SymState Val :=
      { stReab20.sym with
        loans := [⟨0, .activeMut, ⟨v30, .unborrowed⟩,
                   .direct (.localReg 1) []⟩] }
    let stSynced30 : PaddedSymMemState :=
      { stReab20 with sym := symUnsynced30, mem := memOf 30 true }
    let stEnded30 : PaddedSymMemState :=
      { stSynced30 with
        sym :=
          { locals := [⟨.unit, .unborrowed⟩, ⟨v30, .unborrowed⟩,
                       ⟨mirEncodeRef 0 [], .unborrowed⟩]
            loans := [⟨0, .ended, ⟨v30, .unborrowed⟩,
                       .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 2 } }
    let stSynced40 : PaddedSymMemState :=
      { stEnded30 with
        sym :=
          { stEnded30.sym with
            locals := [⟨.unit, .unborrowed⟩, ⟨v40, .unborrowed⟩,
                       ⟨mirEncodeRef 0 [], .unborrowed⟩] }
        mem := memOf 40 true }
    let stDead : PaddedSymMemState :=
      { sym :=
          { stEnded30.sym with
            locals := [⟨.unit, .unborrowed⟩, ⟨.unit, .unborrowed⟩,
                       ⟨mirEncodeRef 0 [], .unborrowed⟩] }
        mirLocalTypes := mirTys
        mirLocals := [.immediate (some .unit), .dead,
                      .immediate (some (mirEncodeRef 0 []))]
        mem := memOf 40 false
        memBlocks := []
        promotedLocals := [] }
    freezePaddedToMem u32SyncCtx 0 u32MemCodec u32MemCodec_lawful st0 = .ok stPinned ∧
    allPromotedLocalsMemSynced u32SyncCtx stPinned = true ∧
    evalPaddedMirOperand u32SyncCtx stPinned (.copy ⟨1, []⟩) = .ok (v10, stPinned) ∧
    mutatePaddedInMem u32SyncCtx 1 1 0 2 (u32MemEncode (BitVec.ofNat 32 20)) stPinned =
      .ok stMut20 ∧
    reabsorbPaddedFromMem u32SyncCtx 0 stMut20 = .ok stReab20 ∧
    allPromotedLocalsMemSynced u32SyncCtx stReab20 = true ∧
    evalPaddedMirOperand u32SyncCtx stReab20 (.copy ⟨1, []⟩) = .ok (v20, stReab20) ∧
    -- Direct unsynchronized symbolic write flips `allPromotedLocalsMemSynced`
    -- to `false` and rejects stale MIR reads with `.error .unsupported`.
    writePlaceVal mirValAlg (.derefSub 2 []) v30 stReab20.sym =
      some symUnsynced30 ∧
    allPromotedLocalsMemSynced u32SyncCtx { stReab20 with sym := symUnsynced30 } = false ∧
    evalPaddedMirOperand u32SyncCtx { stReab20 with sym := symUnsynced30 }
      (.copy ⟨1, []⟩) = .error .unsupported ∧
    evalPaddedMirOperand u32SyncCtx { stReab20 with sym := symUnsynced30 }
      (.copy ⟨0, []⟩) = .error .unsupported ∧
    evalPaddedMirOperand u32SyncCtx { stReab20 with promotedLocals := [] }
      (.copy ⟨1, []⟩) = .error .unsupported ∧
    -- `writePaddedSymPlace` and `endPaddedLoan` synchronize `st.mem` and
    -- `evalPaddedMirOperand` reads the updated `u32` values (`30`, `40`).
    writePaddedSymPlace u32SyncCtx (.derefSub 2 []) v30 stReab20 = .ok stSynced30 ∧
    allPromotedLocalsMemSynced u32SyncCtx stSynced30 = true ∧
    evalPaddedMirOperand u32SyncCtx stSynced30 (.copy ⟨1, []⟩) = .ok (v30, stSynced30) ∧
    Trusted.MirSemantics.evalPrimitiveOperand
      (stSynced30.mirLocalTypes.map SpatialTargetSpec.toCapturedMirTy)
      stSynced30.mirLocals stSynced30.mem (.copy ⟨1, []⟩) =
        .ok (v30, stSynced30.mirLocals, stSynced30.mem) ∧
    evalPaddedMirOperand u32SyncCtx stSynced30 (.move ⟨1, []⟩) = .error .unsupported ∧
    endPaddedLoan u32SyncCtx 0 stSynced30 = .ok stEnded30 ∧
    allPromotedLocalsMemSynced u32SyncCtx stEnded30 = true ∧
    writePaddedSymPlace u32SyncCtx (.localSub 1 []) v40 stEnded30 = .ok stSynced40 ∧
    allPromotedLocalsMemSynced u32SyncCtx stSynced40 = true ∧
    evalPaddedMirOperand u32SyncCtx stSynced40 (.copy ⟨1, []⟩) = .ok (v40, stSynced40) ∧
    deallocatePromotedLocal u32SyncCtx 1 stSynced40 = .ok stDead ∧
    stDead.promotedLocals = [] ∧
    allPromotedLocalsMemSynced u32SyncCtx stDead = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← execEvalPrimitiveOperand_eq]
  rfl

/-- Verifies unpromoted `LocalSlot.immediate` synchronization and `Operand.move`
rejection (`everySlotCoherentWithSym`, `refreshImmediateMirLocals`,
`evalPaddedMirOperand`), `LoanPhase.spatialPinned` authentication of
`st.memBlocks` inside `allPromotedLocalsMemSynced`, `targetSpecLayoutAndMask`
rejection of `.ref`, general `.tuple`, `.rawPtr _ .unsupported`, and empty
`.reprCAdt`, and single-cause guard-isolating pairs where only the target guard
differs from a passing state. -/
theorem immediate_sync_memBlocks_auth_and_single_cause_guard_tests :
    let v10 := u32MemToSymVal (BitVec.ofNat 32 10)
    let v20 := u32MemToSymVal (BitVec.ofNat 32 20)
    let mirTysImm : List SpatialTargetSpec :=
      [.mirTy .bool, .mirTy (.int .i32 false)]
    let stImm10 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.bool true, .unborrowed⟩, ⟨v10, .unborrowed⟩]
            loans := []
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := mirTysImm
        mirLocals := [.immediate (some (.bool true)), .immediate (some v10)]
        mem := execMemoryEmpty
        memBlocks := []
        promotedLocals := [] }
    let symImm20 : SymState Val :=
      { stImm10.sym with
        locals := [⟨.bool true, .unborrowed⟩, ⟨v20, .unborrowed⟩] }
    let stImmSynced20 : PaddedSymMemState :=
      { stImm10 with
        sym := symImm20
        mirLocals := [.immediate (some (.bool true)), .immediate (some v20)] }
    let stImmSplit : PaddedSymMemState :=
      { stImmSynced20 with
        sym :=
          { stImmSynced20.sym with
            locals :=
              [⟨.bool true, .unborrowed⟩,
               ⟨v20, .split [([0], .mutLocked 0), ([1], .mutLocked 1)]⟩]
            loans :=
              [⟨0, .activeMut, ⟨.unit, .unborrowed⟩, .direct (.localReg 1) [0]⟩,
               ⟨1, .activeMut, ⟨.unit, .unborrowed⟩, .direct (.localReg 1) [1]⟩] } }
    let st0 := mkSampleU8U32InitState
    let initVal := paddedU8U32MemCodec.encodeToSymVal sampleU8U32Init
    let bWrite :=
      [AllocByte.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    let memTamperBacking : MemoryState :=
      { nextAllocId := 100
        allocations :=
          [⟨1, 2, .mut,
             List.replicate 4 (.init 0 none) ++
               paddedU8U32Encode sampleU8U32Init ++
               List.replicate 4 (.init 0 none),
             true⟩,
           ⟨99, 2, .mut, paddedU8U32Encode sampleU8U32Init, true⟩] }
    let entryReg0 : PromotedLocalEntry :=
      ⟨0, u8U32TargetSpec, ⟨1, 0⟩, ⟨8, 2⟩, u8PadU32Mask, 8032,
       encodeSymOfCodec paddedU8U32MemCodec⟩
    let entryReg1 : PromotedLocalEntry :=
      ⟨1, u8U32TargetSpec, ⟨1, 0⟩, ⟨8, 2⟩, u8PadU32Mask, 8032,
       encodeSymOfCodec paddedU8U32MemCodec⟩
    let stDeallocReg0 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨initVal, .unborrowed⟩, ⟨.unit, .unborrowed⟩]
            loans := []
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [u8U32TargetSpec, .mirTy .unit]
        mirLocals := [.indirect ⟨1, 0⟩, .immediate (some .unit)]
        mem := ⟨2, [⟨1, 2, .mut, paddedU8U32Encode sampleU8U32Init, true⟩]⟩
        memBlocks := []
        promotedLocals := [entryReg0] }
    let stDeallocReg1 : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.unit, .unborrowed⟩, ⟨initVal, .unborrowed⟩]
            loans := []
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [.mirTy .unit, u8U32TargetSpec]
        mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩]
        mem := ⟨2, [⟨1, 2, .mut, paddedU8U32Encode sampleU8U32Init, true⟩]⟩
        memBlocks := []
        promotedLocals := [entryReg1] }
    -- 1. Unpromoted `.immediate` synchronization, `mirLocalTypes` typing,
    --    split-borrow read guard, and `Operand.move` rejection:
    allPromotedLocalsMemSynced immBoolU32Ctx stImm10 = true ∧
    evalPaddedMirOperand immBoolU32Ctx stImm10 (.copy ⟨1, []⟩) = .ok (v10, stImm10) ∧
    evalPaddedMirOperand immBoolU32Ctx stImm10 (.move ⟨1, []⟩) = .error .unsupported ∧
    writePlaceVal mirValAlg (.localSub 1 []) v20 stImm10.sym = some symImm20 ∧
    allPromotedLocalsMemSynced immBoolU32Ctx { stImm10 with sym := symImm20 } = false ∧
    evalPaddedMirOperand immBoolU32Ctx { stImm10 with sym := symImm20 } (.copy ⟨1, []⟩) =
      .error .unsupported ∧
    writePaddedSymPlace immBoolU32Ctx (.localSub 1 []) v20 stImm10 = .ok stImmSynced20 ∧
    allPromotedLocalsMemSynced immBoolU32Ctx stImmSynced20 = true ∧
    evalPaddedMirOperand immBoolU32Ctx stImmSynced20 (.copy ⟨1, []⟩) =
      .ok (v20, stImmSynced20) ∧
    writePaddedSymPlace immBoolU32Ctx (.localSub 1 []) (.bool false) stImm10 = .fail ∧
    writePaddedSymPlace immBoolU32Ctx (.localSub 1 [])
      (.scalar ⟨.i32, false, BitVec.ofNat 128 4294967296⟩) stImm10 = .fail ∧
    allPromotedLocalsMemSynced immBoolU32Ctx
      { stImm10 with
        sym :=
          { stImm10.sym with
            locals := [⟨.bool true, .unborrowed⟩, ⟨.bool false, .unborrowed⟩] }
        mirLocals := [.immediate (some (.bool true)),
                      .immediate (some (.bool false))] } = false ∧
    evalPaddedMirOperand immBoolU32Ctx
      { stImm10 with
        sym :=
          { stImm10.sym with
            locals := [⟨.bool true, .unborrowed⟩, ⟨.bool false, .unborrowed⟩] }
        mirLocals := [.immediate (some (.bool true)),
                      .immediate (some (.bool false))] }
      (.copy ⟨1, []⟩) = .error .unsupported ∧
    allPromotedLocalsMemSynced immBoolRefCtx
      { stImm10 with
        mirLocalTypes := [.mirTy .bool, .mirTy (.ref .mut .unit)] } = false ∧
    allPromotedLocalsMemSynced immBoolU32Ctx stImmSplit = true ∧
    evalPaddedMirOperand immBoolU32Ctx stImmSplit (.copy ⟨0, []⟩) =
      .ok (.bool true, stImmSplit) ∧
    evalPaddedMirOperand immBoolU32Ctx stImmSplit (.copy ⟨1, []⟩) = .error .unsupported ∧
    -- 2. `targetSpecLayoutAndMask` rejects `.ref`, general `.tuple`, unsized
    --    `.rawPtr`, and empty `.reprCAdt`:
    targetSpecLayoutAndMask (.mirTy (.ref .mut .unit)) = none ∧
    targetSpecLayoutAndMask (.mirTy (.tuple [.bool, .bool])) = none ∧
    targetSpecLayoutAndMask (.mirTy (.rawPtr .mut .unsupported)) = none ∧
    targetSpecLayoutAndMask (.reprCAdt 1 []) = none ∧
    -- 3. Unauthenticated `st.memBlocks` rejection (including out-of-bounds
    --    `ownerLocal`, duplicate `blockId`, and tainted unpinned padding)
    --    inside `allPromotedLocalsMemSynced` + single-cause guard-isolating
    --    pairs:
    allPromotedLocalsMemSynced immBoolU32Ctx
      { stImm10 with
        memBlocks := [⟨1, 0, 99, .readWrite, 1, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] } =
      false ∧
    evalPaddedMirOperand immBoolU32Ctx
      { stImm10 with
        memBlocks := [⟨1, 0, 99, .readWrite, 1, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩] }
      (.copy ⟨1, []⟩) = .error .unsupported ∧
    (match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec paddedU8U32MemCodec_lawful st0 with
     | .fail => False
     | .ok stPinned =>
       -- Duplicate `blockId` across distinct owners in `st.memBlocks` fails
       -- `allPromotedLocalsMemSynced`:
       allPromotedLocalsMemSynced sampleBodyCtx
         { stPinned with
           memBlocks :=
             stPinned.memBlocks ++
               [⟨1, 9, 99, .readWrite, 1, 0, ⟨8, 2⟩, ⟨99, 0⟩, 8032⟩] } = false ∧
       -- Baseline single-cause reference state (`stPinned` itself passes both
       -- `mutatePaddedInMem` and `reabsorbPaddedFromMem`):
       (match mutatePaddedInMem sampleBodyCtx 1 1 4 2 bWrite stPinned with
        | .ok _ => True
        | .fail => False) ∧
       (match reabsorbPaddedFromMem sampleBodyCtx 0 stPinned with
        | .fail => False
        | .ok stReab =>
          -- Forged `memBlocks` entry when loan `0` is `.activeMut` (not
          -- `.spatialPinned`) flips `allPromotedLocalsMemSynced` to `false`,
          -- and provenance-tainted padding on an unpinned promoted allocation
          -- is rejected by `allPromotedLocalsMemSynced` and repaired by
          -- `syncPromotedLocalsToMem`:
          allPromotedLocalsMemSynced sampleBodyCtx stReab = true ∧
          allPromotedLocalsMemSynced sampleBodyCtx
            { stReab with memBlocks := stPinned.memBlocks } = false ∧
          evalPaddedMirOperand sampleBodyCtx
            { stReab with memBlocks := stPinned.memBlocks } (.copy ⟨0, []⟩) =
              .error .unsupported ∧
          allPromotedLocalsMemSynced immBoolU32Ctx
            { stImm10 with memBlocks := stPinned.memBlocks } = false ∧
          (match execWriteBytes stReab.mem ⟨1, 1⟩ 0 [AllocByte.init 0 (some 7)] with
           | .error _ => False
           | .ok memPadProv =>
             allPromotedLocalsMemSynced sampleBodyCtx { stReab with mem := memPadProv } = false ∧
             match syncPromotedLocalsToMem sampleBodyCtx { stReab with mem := memPadProv } with
             | .ok stRepaired => allPromotedLocalsMemSynced sampleBodyCtx stRepaired = true
             | .fail => False)) ∧
       -- Single-cause pair A: only `place := ⟨99, 0⟩` perturbed (`mirLocals[2]`
       -- unchanged):
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 bWrite
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨99, 0⟩,
                         .immediate (some (mirEncodeRef 0 []))]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨99, 0⟩ }) } =
         .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨99, 0⟩,
                         .immediate (some (mirEncodeRef 0 []))]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨99, 0⟩ }) } =
         .fail ∧
       -- Single-cause pair B: only `place := ⟨1, 4⟩` perturbed (`mirLocals[2]`
       -- unchanged):
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 bWrite
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩,
                         .immediate (some (mirEncodeRef 0 []))]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨1, 4⟩ }) } =
         .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           mem := memTamperBacking
           mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩,
                         .immediate (some (mirEncodeRef 0 []))]
           memBlocks := stPinned.memBlocks.map (fun b => { b with place := ⟨1, 4⟩ }) } =
         .fail ∧
       -- Single-cause pair C: only `ownerLocal := 2` perturbed (`mirLocals`
       -- unchanged):
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 bWrite
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with ownerLocal := 2 }) } =
         .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           memBlocks := stPinned.memBlocks.map (fun b => { b with ownerLocal := 2 }) } =
         .fail ∧
       -- Single-cause pair D: only `mirLocals[1] := .dead` perturbed
       -- (`mirLocals[2]` unchanged):
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 bWrite
         { stPinned with
           mirLocals := [.immediate (some .unit), .dead,
                         .immediate (some (mirEncodeRef 0 []))] } = .fail ∧
       reabsorbPaddedFromMem sampleBodyCtx 0
         { stPinned with
           mirLocals := [.immediate (some .unit), .dead,
                         .immediate (some (mirEncodeRef 0 []))] } = .fail) ∧
    -- Single-cause pair E: `deallocatePromotedLocal` rejects `reg = 0` while
    -- accepting the identical unborrowed promoted state at `reg = 1`:
    deallocatePromotedLocal deallocReg0Ctx 0 stDeallocReg0 = .fail ∧
    (match deallocatePromotedLocal u8U32Ctx2 1 stDeallocReg1 with
     | .ok _ => True
     | .fail => False) ∧
    -- Single-cause pair F: `liveMutSliceValid` enforces alignment even on
    -- zero-sized layouts (`⟨0, 2⟩`):
    liveMutSliceValid ⟨2, [⟨1, 2, .mut, [], true⟩]⟩ ⟨1, 0⟩ ⟨0, 2⟩ = true ∧
    liveMutSliceValid ⟨2, [⟨1, 0, .mut, [], true⟩]⟩ ⟨1, 0⟩ ⟨0, 2⟩ = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl,
    rfl, rfl, rfl, rfl,
    rfl, rfl,
    ⟨rfl, trivial, ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, trivial, rfl, rfl⟩

/-- Verifies: (1) `mutatePaddedInMem` provenance conservation (rejects forged
`some aid` provenance on both `U8U32Struct` and `ProvPtrStruct`, rejects
harvesting provenance synthetically placed in padding bytes, and accepts
in-place pointer-offset mutation preserving an existing non-padding provenance
tag); (2) `reabsorbPaddedFromMem` codec-independent post-decode authentication
(rejects a tampered `.spatialPinned` witness preserving `codecId` and `encode
.unit` whose decoder returns a spoofed handle-free scalar value); (3)
`promotedEntryMemSynced` rejects a synthetically lowered `entry.layout`
alignment; and (4) `evalPaddedMirOperand` distinguishes shared-borrow model
tracking (`.error .unsupported`) from uninitialized immediate reads (`.error
.undefined`). -/
theorem mutate_prov_conservation_and_decoder_auth_tests :
    let st0 := mkSampleU8U32InitState
    let stPtr0 := mkProvInitState 7
    let spoofedVal :=
      paddedU8U32MemCodec.encodeToSymVal ⟨0x99, BitVec.ofNat 32 0xDEADBEEF⟩
    let bForgedU32 : List AllocByte :=
      [.init 1 (some 7), .init 2 none, .init 3 none, .init 4 none]
    let bCleanU32 : List AllocByte :=
      [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
    let ptrOff18Bytes : List AllocByte :=
      (execEncodeUInt execProfileTargetEndian 8 0x18).map
        (fun b => AllocByte.init b (some 7))
    let ptrForged99Bytes : List AllocByte :=
      (execEncodeUInt execProfileTargetEndian 8 0x18).map
        (fun b => AllocByte.init b (some 99))
    let expectedPtr18Val :=
      (provPtrPaddedMemCodec 7).encodeToSymVal ⟨0x10, BitVec.ofNat 64 0x18⟩
    -- 1. `U8U32Struct`: forged provenance rejected; clean write succeeds;
    --    synthetically tainted padding cannot be harvested as provenance;
    --    tampered scalar-spoofing witness matching `witnessMatchesBlock` and
    --    `replaceableVal` is rejected by `reabsorbPaddedFromMem`:
    (match freezePaddedToMem sampleBodyCtx 0 paddedU8U32MemCodec
        paddedU8U32MemCodec_lawful st0 with
     | .fail => False
     | .ok stPinned =>
       let origWitness := paddedLoanWitnessCodec paddedU8U32MemCodec 1 ⟨1, 0⟩
       let tamperedScalarSpoofingWitness : SpatialCodec Val :=
         { codecId := origWitness.codecId
           encode := origWitness.encode
           decode := fun cells =>
             match cells with
             | [.init v, .uninit, .init _] => some v
             | [.uninit, .init (.bytes _)] => some spoofedVal
             | _ => none
           decode_encode := fun _ => rfl }
       let stSpoof : PaddedSymMemState :=
         { stPinned with
           sym :=
             { stPinned.sym with
               loans :=
                 updateLoan 0
                   (fun x =>
                     ⟨x.id, .spatialPinned 1 tamperedScalarSpoofingWitness,
                      x.cell, x.target⟩)
                   stPinned.sym.loans } }
       mutatePaddedInMem sampleBodyCtx 1 1 4 2 bForgedU32 stPinned = .fail ∧
       (match mutatePaddedInMem sampleBodyCtx 1 1 4 2 bCleanU32 stPinned with
        | .ok _ => True
        | .fail => False) ∧
       (match execWriteBytes stPinned.mem ⟨1, 1⟩ 0 [.init 0 (some 7)] with
        | .error _ => False
        | .ok memPadTainted =>
          mutatePaddedInMem sampleBodyCtx 1 1 0 0 [.init 0x11 (some 7)]
            { stPinned with mem := memPadTainted } = .fail) ∧
       witnessMatchesBlock tamperedScalarSpoofingWitness 1
         ⟨1, 0, 1, .readWrite, 1, 0, ⟨8, 2⟩, ⟨1, 0⟩, 8032⟩ = true ∧
       replaceableVal mirValAlg stSpoof.sym.loans
         (paddedU8U32MemCodec.encodeToSymVal sampleU8U32Init) spoofedVal = true ∧
       reabsorbPaddedFromMem sampleBodyCtx 0 stSpoof = .fail) ∧
    -- 2. `ProvPtrStruct`: mutating pointer offset while preserving existing
    --    non-padding provenance `some 7` succeeds and reabsorbs to offset
    --    `0x18`, while forging `some 99` fails closed:
    (match freezePaddedToMem (provBodyCtx 7) 0 (provPtrPaddedMemCodec 7)
        (provPtrPaddedMemCodec_lawful 7) stPtr0 with
     | .fail => False
     | .ok stPtrPinned =>
       mutatePaddedInMem (provBodyCtx 7) 1 1 8 3 ptrForged99Bytes stPtrPinned =
         .fail ∧
       match mutatePaddedInMem (provBodyCtx 7) 1 1 8 3 ptrOff18Bytes
           stPtrPinned with
       | .fail => False
       | .ok stPtrMut =>
         match reabsorbPaddedFromMem (provBodyCtx 7) 0 stPtrMut with
         | .fail => False
         | .ok stPtrReab =>
           match findLoan 0 stPtrReab.sym.loans with
           | some le => mirValBeqAt 8 le.cell.val expectedPtr18Val = true
           | none => False) ∧
    -- 3. Single-cause `promotedEntryMemSynced` guards (positive baseline vs.
    --    lowered `alignLog2`, non-zero `place.offset`, and wrong `padMask`)
    --    and shared-borrowed vs. uninitialized immediate reads:
    (let v10 := u32MemToSymVal (BitVec.ofNat 32 10)
     let stGoodU32 : PaddedSymMemState :=
       { sym :=
           { locals := [⟨.unit, .unborrowed⟩, ⟨v10, .unborrowed⟩]
             loans := []
             regionGroups := []
             regionDeposits := []
             spatial := []
             nextSpatialTag := 1 }
         mirLocalTypes := [.mirTy .unit, .mirTy (.int .i32 false)]
         mirLocals := [.immediate (some .unit), .indirect ⟨1, 0⟩]
         mem := ⟨2, [⟨1, 2, .mut, u32MemEncode (BitVec.ofNat 32 10), true⟩]⟩
         memBlocks := []
         promotedLocals :=
           [⟨1, .mirTy (.int .i32 false), ⟨1, 0⟩, ⟨4, 2⟩,
             u32MemCodec.padMask, u32MemCodec.codecId,
             encodeSymOfCodec u32MemCodec⟩] }
     let stTamperedAlign : PaddedSymMemState :=
       { stGoodU32 with
         mem := ⟨2, [⟨1, 0, .mut, u32MemEncode (BitVec.ofNat 32 10), true⟩]⟩
         promotedLocals :=
           [⟨1, .mirTy (.int .i32 false), ⟨1, 0⟩, ⟨4, 0⟩,
             u32MemCodec.padMask, u32MemCodec.codecId,
             encodeSymOfCodec u32MemCodec⟩] }
     let stTamperedOffset : PaddedSymMemState :=
       { stGoodU32 with
         mirLocals := [.immediate (some .unit), .indirect ⟨1, 4⟩]
         mem :=
           ⟨2,
            [⟨1, 2, .mut,
              u32MemEncode (BitVec.ofNat 32 0) ++
                u32MemEncode (BitVec.ofNat 32 10),
              true⟩]⟩
         promotedLocals :=
           [⟨1, .mirTy (.int .i32 false), ⟨1, 4⟩, ⟨4, 2⟩,
             u32MemCodec.padMask, u32MemCodec.codecId,
             encodeSymOfCodec u32MemCodec⟩] }
     let stTamperedPadMask : PaddedSymMemState :=
       { stGoodU32 with
         promotedLocals :=
           [⟨1, .mirTy (.int .i32 false), ⟨1, 0⟩, ⟨4, 2⟩,
             [true, false, false, false], u32MemCodec.codecId,
             encodeSymOfCodec u32MemCodec⟩] }
     let stSharedImm : PaddedSymMemState :=
       { sym :=
           { locals := [⟨.bool true, .unborrowed⟩, ⟨v10, .shared [0]⟩]
             loans :=
               [⟨0, .activeShared, ⟨v10, .unborrowed⟩, .direct (.localReg 1) []⟩]
             regionGroups := []
             regionDeposits := []
             spatial := []
             nextSpatialTag := 1 }
         mirLocalTypes := [.mirTy .bool, .mirTy (.int .i32 false)]
         mirLocals := [.immediate (some (.bool true)), .immediate (some v10)]
         mem := execMemoryEmpty
         memBlocks := []
         promotedLocals := [] }
     let stDesyncedUninitImm : PaddedSymMemState :=
       { sym :=
           { locals := [⟨.bool true, .unborrowed⟩, ⟨v10, .unborrowed⟩]
             loans := []
             regionGroups := []
             regionDeposits := []
             spatial := []
             nextSpatialTag := 1 }
         mirLocalTypes := [.mirTy .bool, .mirTy (.int .i32 false)]
         mirLocals := [.immediate (some (.bool true)), .immediate none]
         mem := execMemoryEmpty
         memBlocks := []
         promotedLocals := [] }
     let stUninitImm : PaddedSymMemState :=
       { stDesyncedUninitImm with
         sym :=
           { stDesyncedUninitImm.sym with
             locals := [⟨.bool true, .unborrowed⟩, ⟨.unit, .unborrowed⟩] } }
     allPromotedLocalsMemSynced unitU32Ctx stGoodU32 = true ∧
     allPromotedLocalsMemSynced unitU32Ctx stTamperedAlign = false ∧
     liveMutSliceValid stTamperedOffset.mem ⟨1, 4⟩ ⟨4, 2⟩ = true ∧
     allPromotedLocalsMemSynced unitU32Ctx stTamperedOffset = false ∧
     allPromotedLocalsMemSynced unitU32Ctx stTamperedPadMask = false ∧
     allPromotedLocalsMemSynced immBoolU32Ctx stSharedImm = true ∧
     evalPaddedMirOperand immBoolU32Ctx stSharedImm (.copy ⟨1, []⟩) =
       .error .unsupported ∧
     allPromotedLocalsMemSynced immBoolU32Ctx stDesyncedUninitImm = false ∧
     evalPaddedMirOperand immBoolU32Ctx stDesyncedUninitImm (.copy ⟨1, []⟩) =
       .error .unsupported ∧
     allPromotedLocalsMemSynced immBoolU32Ctx stUninitImm = true ∧
     evalPaddedMirOperand immBoolU32Ctx stUninitImm (.copy ⟨1, []⟩) =
       .error .undefined) := by
  exact ⟨⟨rfl, trivial, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Verifies: (1) `BodySpatialCtx` captured-MIR authentication rejects
mislabeled scalar types (`u32` claimed as `.bool`), unauthenticated
`.unsupported` locals claimed as `.reprCAdt`, single-cause mismatches on
`adtTag`, field layout, `bodyIdentity`, empty `body.identity`, duplicate
`adtLocals` entries, and ADT-authenticated slots mislabeled as `.mirTy
.unsupported`; (2) `allPromotedLocalsMemSynced`, `writePaddedSymPlace`, and
`endPaddedLoan` initialize unpromoted `.immediate none` slots on whole-local
`immValCompatWithTargetSpec` writes while rejecting non-`.unit` symbolic cells
over `.dead` slots, `.dead` targets, `.immediate none` sub-path writes (even
when the symbolic cell is a projectable tuple), and active loans targeting
`.dead` or `.immediate none` MIR slots; and (3) aliased `AllocId`s shared
independently through either a second `PromotedLocalEntry` or a second
`LocalSlot.indirect` local fail closed across `allPromotedLocalsMemSynced`,
`mutatePaddedInMem`, and `reabsorbPaddedFromMem`.
-/
theorem body_ctx_auth_uninit_dead_writes_and_aliased_alloc_tests :
    let v10 := u32MemToSymVal (BitVec.ofNat 32 10)
    let boolClaimSt : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.unit, .unborrowed⟩, ⟨.bool true, .mutLocked 0⟩]
            loans :=
              [⟨0, .activeMut, ⟨.bool true, .unborrowed⟩,
                .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [.mirTy .unit, .mirTy .bool]
        mirLocals := [.immediate (some .unit), .immediate (some (.bool true))]
        mem := execMemoryEmpty
        memBlocks := []
        promotedLocals := [] }
    let ctxUnauthUnsupported : BodySpatialCtx :=
      { body :=
          { argumentCount := 0
            locals := [.unit, .unsupported, .ref .mut .unsupported]
            basicBlocks := [{ statements := [], terminator := .return_ }]
            isUnsafe := false
            identity := "unauth_adt_fn" }
        adtLocals := [] }
    let ctxWrongTag : BodySpatialCtx :=
      { sampleBodyCtx with
        adtLocals :=
          [⟨"sample_u8_u32", 1, 9999,
            [⟨0, .int .i8 false⟩, ⟨4, .int .i32 false⟩]⟩] }
    let ctxWrongBodyId : BodySpatialCtx :=
      { sampleBodyCtx with
        adtLocals :=
          [⟨"other_fn", 1, 8032,
            [⟨0, .int .i8 false⟩, ⟨4, .int .i32 false⟩]⟩] }
    let ctxEmptyId : BodySpatialCtx :=
      { sampleBodyCtx with
        body := { sampleBodyCtx.body with identity := "" }
        adtLocals :=
          [⟨"", 1, 8032,
            [⟨0, .int .i8 false⟩, ⟨4, .int .i32 false⟩]⟩] }
    let ctxDupEntry : BodySpatialCtx :=
      { sampleBodyCtx with
        adtLocals := sampleBodyCtx.adtLocals ++ sampleBodyCtx.adtLocals }
    let ctxWrongFields : BodySpatialCtx :=
      { sampleBodyCtx with
        adtLocals :=
          [⟨"sample_u8_u32", 1, 8032,
            [⟨0, .int .i8 false⟩, ⟨8, .int .i32 false⟩]⟩] }
    let stUninitImm : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.bool true, .unborrowed⟩, ⟨.unit, .unborrowed⟩]
            loans := []
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [.mirTy .bool, .mirTy (.int .i32 false)]
        mirLocals := [.immediate (some (.bool true)), .immediate none]
        mem := execMemoryEmpty
        memBlocks := []
        promotedLocals := [] }
    let stUninitTupleSubwrite : PaddedSymMemState :=
      { stUninitImm with
        sym :=
          { stUninitImm.sym with
            locals :=
              [⟨.bool true, .unborrowed⟩,
               ⟨.tuple [.bool true, .bool false], .unborrowed⟩] } }
    let stDeadUnit : PaddedSymMemState :=
      { sym :=
          { locals := [⟨.unit, .unborrowed⟩, ⟨.unit, .unborrowed⟩]
            loans := []
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 1 }
        mirLocalTypes := [.mirTy .unit, .mirTy .unit]
        mirLocals := [.immediate (some .unit), .dead]
        mem := execMemoryEmpty
        memBlocks := []
        promotedLocals := [] }
    let stDeadNonUnit : PaddedSymMemState :=
      { stDeadUnit with
        sym :=
          { stDeadUnit.sym with
            locals := [⟨.unit, .unborrowed⟩, ⟨v10, .unborrowed⟩] } }
    let stLoanOnDead : PaddedSymMemState :=
      { stDeadUnit with
        sym :=
          { stDeadUnit.sym with
            locals := [⟨.unit, .unborrowed⟩, ⟨.unit, .mutLocked 0⟩]
            loans :=
              [⟨0, .activeMut, ⟨.unit, .unborrowed⟩,
                .direct (.localReg 1) []⟩] } }
    let stLoanOnUninit : PaddedSymMemState :=
      { stLoanOnDead with
        mirLocals := [.immediate (some .unit), .immediate none] }
    let ctxTwoU32 : BodySpatialCtx :=
      mkBodyCtxOfSpecs "two_u32"
        [.mirTy .unit, .mirTy (.int .i32 false), .mirTy (.int .i32 false)]
    let witness1 := paddedLoanWitnessCodec u32MemCodec 1 ⟨1, 0⟩
    let blk1 : PaddedSpatialBlock :=
      ⟨1, 0, 1, .readWrite, 1, 0, ⟨4, 2⟩, ⟨1, 0⟩, u32MemCodec.codecId⟩
    let entry1 : PromotedLocalEntry :=
      ⟨1, .mirTy (.int .i32 false), ⟨1, 0⟩, ⟨4, 2⟩, u32MemCodec.padMask,
       u32MemCodec.codecId, encodeSymOfCodec u32MemCodec⟩
    let entry2Aliased : PromotedLocalEntry :=
      ⟨2, .mirTy (.int .i32 false), ⟨1, 0⟩, ⟨4, 2⟩, u32MemCodec.padMask,
       u32MemCodec.codecId, encodeSymOfCodec u32MemCodec⟩
    let stAliasedBase : PaddedSymMemState :=
      { sym :=
          { locals :=
              [⟨.unit, .unborrowed⟩, ⟨v10, .mutLocked 0⟩, ⟨v10, .unborrowed⟩]
            loans :=
              [⟨0, .spatialPinned 1 witness1, ⟨v10, .unborrowed⟩,
                .direct (.localReg 1) []⟩]
            regionGroups := []
            regionDeposits := []
            spatial := []
            nextSpatialTag := 2 }
        mirLocalTypes :=
          [.mirTy .unit, .mirTy (.int .i32 false), .mirTy (.int .i32 false)]
        mirLocals :=
          [.immediate (some .unit), .indirect ⟨1, 0⟩, .immediate (some v10)]
        mem := ⟨2, [⟨1, 2, .mut, u32MemEncode (BitVec.ofNat 32 10), true⟩]⟩
        memBlocks := [blk1]
        promotedLocals := [entry1] }
    let stAliasedPromotedOnly : PaddedSymMemState :=
      { stAliasedBase with promotedLocals := [entry1, entry2Aliased] }
    let stAliasedIndirectOnly : PaddedSymMemState :=
      { stAliasedBase with
        mirLocals :=
          [.immediate (some .unit), .indirect ⟨1, 0⟩, .indirect ⟨1, 0⟩] }
    -- 1. Captured `Body` type authentication:
    specsMatchBodyCtx unitU32Ctx [.mirTy .unit, .mirTy .bool] = false ∧
    allPromotedLocalsMemSynced unitU32Ctx boolClaimSt = false ∧
    evalPaddedMirOperand unitU32Ctx boolClaimSt (.copy ⟨1, []⟩) =
      .error .unsupported ∧
    specsMatchBodyCtx ctxUnauthUnsupported mkSampleU8U32InitState.mirLocalTypes =
      false ∧
    freezePaddedToMem ctxUnauthUnsupported 0 paddedU8U32MemCodec
      paddedU8U32MemCodec_lawful mkSampleU8U32InitState = .fail ∧
    specsMatchBodyCtx ctxWrongTag mkSampleU8U32InitState.mirLocalTypes =
      false ∧
    freezePaddedToMem ctxWrongTag 0 paddedU8U32MemCodec
      paddedU8U32MemCodec_lawful mkSampleU8U32InitState = .fail ∧
    specsMatchBodyCtx ctxWrongBodyId mkSampleU8U32InitState.mirLocalTypes =
      false ∧
    specsMatchBodyCtx ctxEmptyId mkSampleU8U32InitState.mirLocalTypes =
      false ∧
    specsMatchBodyCtx ctxDupEntry mkSampleU8U32InitState.mirLocalTypes =
      false ∧
    specsMatchBodyCtx ctxWrongFields mkSampleU8U32InitState.mirLocalTypes =
      false ∧
    specsMatchBodyCtx sampleBodyCtx
      [.mirTy .unit, .mirTy .unsupported,
       .mirTy (.ref .mut .unsupported)] = false ∧
    -- 2. `.immediate none` whole-local initialization vs. `.dead` / sub-path /
    --    loan-writeback rejection:
    (match writePaddedSymPlace immBoolU32Ctx (.localSub 1 []) v10 stUninitImm with
     | .fail => False
     | .ok stInit =>
       stInit.mirLocals =
         [.immediate (some (.bool true)), .immediate (some v10)] ∧
       allPromotedLocalsMemSynced immBoolU32Ctx stInit = true ∧
       evalPaddedMirOperand immBoolU32Ctx stInit (.copy ⟨1, []⟩) =
         .ok (v10, stInit)) ∧
    writePaddedSymPlace immBoolU32Ctx (.localSub 1 []) (.bool false)
      stUninitImm = .fail ∧
    writePaddedSymPlace immBoolU32Ctx (.localSub 1 [0]) (.bool false)
      stUninitTupleSubwrite = .fail ∧
    allPromotedLocalsMemSynced zstBodyCtx stDeadNonUnit = false ∧
    allPromotedLocalsMemSynced zstBodyCtx stLoanOnDead = false ∧
    writePaddedSymPlace zstBodyCtx (.localSub 0 []) .unit stLoanOnDead =
      .fail ∧
    writePaddedSymPlace zstBodyCtx (.localSub 1 []) .unit stDeadUnit = .fail ∧
    endPaddedLoan zstBodyCtx 0 stLoanOnDead = .fail ∧
    endPaddedLoan zstBodyCtx 0 stLoanOnUninit = .fail ∧
    -- 3. Single-cause aliased `AllocId` guards (`otherPromotedEntryUsesAlloc`
    --    and `otherIndirectLocalUsesAlloc`) fail closed independently:
    allPromotedLocalsMemSynced ctxTwoU32 stAliasedBase = true ∧
    allPromotedLocalsMemSynced ctxTwoU32 stAliasedPromotedOnly = false ∧
    mutatePaddedInMem ctxTwoU32 1 1 0 2 (u32MemEncode (BitVec.ofNat 32 20))
      stAliasedPromotedOnly = .fail ∧
    reabsorbPaddedFromMem ctxTwoU32 0 stAliasedPromotedOnly = .fail ∧
    allPromotedLocalsMemSynced ctxTwoU32 stAliasedIndirectOnly = false ∧
    mutatePaddedInMem ctxTwoU32 1 1 0 2 (u32MemEncode (BitVec.ofNat 32 20))
      stAliasedIndirectOnly = .fail ∧
    reabsorbPaddedFromMem ctxTwoU32 0 stAliasedIndirectOnly = .fail := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift

end
