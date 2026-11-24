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
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.PureLift.Lens
public import Anneal.PureLift.PermTree
public import Anneal.PureLift.LoanGraph
public import Anneal.PureLift.SpatialPin
public import Anneal.PureLift.SpatialMem.MirMemMirror

public section

namespace Anneal.PureLift

open Trusted.MirAst Trusted.MirSemantics

/-!
# Tagged `u32` `SpatialCodec` Instantiation (`ValByteCodec`)

Instantiates `SpatialCodec Val` (`u32TaggedByteCodec`) over computable
`MirSemantics` byte codecs with a constructive `LawfulCodec` proof and a framed
`freezeToSpatialInState` / `mutateSpatialInState` / `reabsorbFromSpatialInState`
`SpatialTriple` lifecycle.
-/

/-! ## Tagged `u32` `SpatialCodec` Instantiation -/

/-- True iff `v` is a canonical unsigned 32-bit scalar (`u32`). -/
@[expose] def isValidU32Val : Val → Bool
  | .scalar sv =>
    match sv.width with
    | .i32 => (!sv.signed) && Nat.blt sv.bits.toNat 4294967296
    | .i8 | .i16 | .i64 | .i128 | .isize => false
  | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
  | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
    false

/-- Encodes canonical `u32` values into four `.rawByte` cells and wraps all
other `Val` inputs with a 2-cell `[.rawByte 1, .init v]` tag. -/
@[expose] def u32TaggedEncode (v : Val) : List (CellVal Val) :=
  match v with
  | .scalar sv =>
    match sv.width with
    | .i32 =>
      if (!sv.signed) && Nat.blt sv.bits.toNat 4294967296 then
        (execEncodeUInt execProfileTargetEndian 4 sv.bits.toNat).map
          CellVal.rawByte
      else
        [.rawByte 1, .init v]
    | .i8 | .i16 | .i64 | .i128 | .isize => [.rawByte 1, .init v]
  | .ptr _ | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ | .tuple _
  | .array _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _ | .bytes _ =>
    [.rawByte 1, .init v]

/-- Decodes four `.rawByte` cells back into a `u32` scalar or unwraps a
non-`u32` 2-cell tagged representation, rejecting non-canonical encodings. -/
@[expose] def u32TaggedDecode (cells : List (CellVal Val)) : Option Val :=
  match cells with
  | [c0, c1] =>
    match c0 with
    | .rawByte tag =>
      match c1 with
      | .init v =>
        if Nat.beq tag.toNat 1 && !isValidU32Val v then some v else none
      | .uninit | .rawByte _ => none
    | .init _ | .uninit => none
  | [c0, c1, c2, c3] =>
    match c0 with
    | .rawByte b0 =>
      match c1 with
      | .rawByte b1 =>
        match c2 with
        | .rawByte b2 =>
          match c3 with
          | .rawByte b3 =>
            some (.scalar ⟨.i32, false,
              BitVec.ofNat 128 (execDecodeUInt execProfileTargetEndian [b0, b1, b2, b3])⟩)
          | .init _ | .uninit => none
        | .init _ | .uninit => none
      | .init _ | .uninit => none
    | .init _ | .uninit => none
  | [] | [_] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => none

private theorem u32TaggedDecode_map_rawByte4 :
    ∀ (xs : List UInt8), xs.length = 4 →
      u32TaggedDecode (xs.map CellVal.rawByte) =
        some (.scalar ⟨.i32, false,
          BitVec.ofNat 128 (execDecodeUInt execProfileTargetEndian xs)⟩)
  | [_b0, _b1, _b2, _b3], _ => rfl
  | [], h => nomatch h
  | [_], h => nomatch h
  | [_, _], h => nomatch h
  | [_, _, _], h => nomatch h
  | _ :: _ :: _ :: _ :: _ :: _, h => nomatch h

/-- Round-trip decoding of `u32TaggedEncode`. -/
theorem u32TaggedDecode_u32TaggedEncode (v : Val) :
    u32TaggedDecode (u32TaggedEncode v) = some v := by
  cases v with
  | ptr _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _
  | array _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bytes _ =>
    rfl
  | scalar sv =>
    cases sv with
    | mk width signed bits =>
      cases width with
      | i8 | i16 | i64 | i128 | isize => rfl
      | i32 =>
        dsimp only [u32TaggedEncode]
        cases hSigned : signed with
        | true => rfl
        | false =>
          rw [Bool.not_false, Bool.true_and]
          cases hLt : Nat.blt bits.toNat 4294967296 with
          | false =>
            rw [ite_bool_false rfl]
            dsimp only [u32TaggedDecode]
            have hCond : (Nat.beq (1 : UInt8).toNat 1 &&
                !isValidU32Val (.scalar ⟨.i32, false, bits⟩)) = true := by
              dsimp only [isValidU32Val]
              rw [Bool.not_false, Bool.true_and, hLt]
              rfl
            rw [ite_bool_true hCond]
          | true =>
            rw [ite_bool_true rfl]
            have hLen : (execEncodeUInt execProfileTargetEndian 4 bits.toNat).length = 4 :=
              execEncodeUInt_length execProfileTargetEndian 4 bits.toNat
            rw [u32TaggedDecode_map_rawByte4 _ hLen]
            have hPow4 : Nat.pow 256 4 = 4294967296 := rfl
            have hNatLt : bits.toNat < Nat.pow 256 4 := by
              rw [hPow4]
              exact natLt_of_blt bits.toNat 4294967296 hLt
            rw [decodeUInt_encodeUInt_of_lt execProfileTargetEndian 4 bits.toNat hNatLt]
            have hBv : BitVec.ofNat 128 bits.toNat = bits := by
              cases bits with
              | ofFin f =>
                cases f with
                | mk v hv =>
                  have hMod : Nat.mod v (Nat.pow 2 128) = v := natMod_eq_of_lt hv
                  have hFinGen :
                      ∀ (a : Nat) (ha : a < Nat.pow 2 128),
                        a = v → (Fin.mk a ha : Fin (Nat.pow 2 128)) = Fin.mk v hv := by
                    intro a ha hEq
                    subst hEq
                    rfl
                  exact congrArg BitVec.ofFin
                    (hFinGen (Nat.mod v (Nat.pow 2 128))
                      (Nat.mod_lt v (Nat.pow_pos (Nat.zero_lt_succ 1))) hMod)
            rw [hBv]

/-- Total `SpatialCodec Val` mapping `u32` scalars to four target-endian
`.rawByte` cells. -/
@[expose] def u32TaggedByteCodec : SpatialCodec Val where
  codecId := 32
  encode := u32TaggedEncode
  decode := u32TaggedDecode
  decode_encode := u32TaggedDecode_u32TaggedEncode

/-- Constructive round-trip lawfulness witness for `u32TaggedByteCodec`. -/
theorem u32TaggedByteCodec_lawful :
    LawfulCodec u32TaggedByteCodec :=
  u32TaggedByteCodec.decode_encode

private theorem hasUninitCell_map_rawByte {V : Type} (xs : List UInt8) :
    hasUninitCell (xs.map (@CellVal.rawByte V)) = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem listAppend_singleton {α : Type} (x : α) (xs : List α) :
    [x] ++ xs = x :: xs := rfl

private theorem listFoldr_cons {α β : Type} (f : α → β → β) (z : β) (x : α) (xs : List α) :
    (x :: xs).foldr f z = f x (xs.foldr f z) := rfl

private theorem listFoldr_nil {α β : Type} (f : α → β → β) (z : β) :
    ([] : List α).foldr f z = z := rfl

private theorem natEq_of_beqOp (a b : Nat) (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

private theorem natBeqOp_refl (a : Nat) : (a == a) = true :=
  decide_eq_true rfl

private theorem natBeqOp_eq_true_of_eq (a b : Nat) (h : a = b) : (a == b) = true :=
  decide_eq_true h

private theorem mutateSpatialBlockAt_foldr_disjoint
    (bid tag : Nat) (newCells : List (CellVal Val))
    (step : SpatialBlock Val →
      Bool × Bool × List (SpatialBlock Val) →
      Bool × Bool × List (SpatialBlock Val))
    (hStep : ∀ b dup found rest,
      step b (dup, found, rest) =
        if (b.blockId == bid) = true then
          if found = true then (true, true, rest)
          else
            if ((b.provenanceTag == tag &&
                  (match b.perm with | .readWrite => true | .readOnly => false)) &&
                 b.activeSubSplits == 0 &&
                 newCells.length == b.cells.length) = true then
              (dup, true,
                { blockId := b.blockId, originLoan := b.originLoan, perm := b.perm,
                  provenanceTag := b.provenanceTag, activeSubSplits := b.activeSubSplits,
                  cells := newCells } :: rest)
            else (true, true, rest)
        else (dup, found, b :: rest)) :
    ∀ (hFrame : List (SpatialBlock Val)),
      (∀ b, b ∈ hFrame → b.blockId ≠ bid) →
      hFrame.foldr step (false, false, []) = (false, false, hFrame)
  | [], _ => rfl
  | b :: bs, hDisj => by
    have hbNe : b.blockId ≠ bid := hDisj b (List.Mem.head bs)
    have hBeq : (b.blockId == bid) = false := by
      cases hEq : b.blockId == bid with
      | false => rfl
      | true => exact False.elim (hbNe (natEq_of_beqOp b.blockId bid hEq))
    have hTail := mutateSpatialBlockAt_foldr_disjoint bid tag newCells step hStep bs
      (fun x hx => hDisj x (List.Mem.tail b hx))
    rw [listFoldr_cons, hTail, hStep b false false bs, ite_bool_false hBeq]

/-- Singleton spatial points-to assertion binding `blockId`, `provenanceTag`,
`perm`, `activeSubSplits = 0`, and `cells`. -/
@[expose] def spatialPointsToTagged (bid tag : Nat)
    (perm : SpatialPerm)
    (cells : List (CellVal Val)) : SpatialProp Val :=
  fun blocks =>
    match blocks with
    | [] => False
    | b :: rest =>
      match rest with
      | [] => spatialPointsTo bid perm cells [b] ∧ b.provenanceTag = tag
      | _ :: _ => False

/-- Separation-logic `SpatialTriple` for `mutateSpatialBlockAt` preserving
disjoint spatial frames. -/
theorem mutateSpatialBlockAt_pointsTo_triple
    (bid tag : Nat)
    (oldCells newCells : List (CellVal Val))
    (hLen : newCells.length = oldCells.length) :
    SpatialTriple
      (spatialPointsToTagged bid tag .readWrite oldCells)
      (mutateSpatialBlockAt bid tag newCells)
      (spatialPointsToTagged bid tag .readWrite newCells) := by
  intro h hFrame hDisj hPre
  cases h with
  | nil => exact False.elim hPre
  | cons blk rest =>
    cases rest with
    | cons _ _ => exact False.elim hPre
    | nil =>
      have hPt := hPre.1
      have hBid : blk.blockId = bid := hPt.1
      have hPerm : blk.perm = .readWrite := hPt.2.1
      have hSplits : blk.activeSubSplits = 0 := hPt.2.2.1
      have hCells : blk.cells = oldCells := hPt.2.2.2
      have hTag : blk.provenanceTag = tag := hPre.2
      have hDisjIds : ∀ b, b ∈ hFrame → b.blockId ≠ bid := by
        intro bf hMem
        have hPair := hDisj blk bf (List.Mem.head []) hMem
        rw [hBid] at hPair
        exact fun hEq => hPair.1 hEq.symm
      cases blk with
      | mk bId orig bPerm pTag splits cells =>
        dsimp only at hBid hPerm hSplits hCells hTag
        subst hBid
        subst hPerm
        subst hSplits
        subst hCells
        subst hTag
        let blk' : SpatialBlock Val :=
          ⟨bId, orig, .readWrite, pTag, 0, newCells⟩
        refine ⟨[blk'], ?_, ?_, ?_⟩
        · dsimp only [mutateSpatialBlockAt]
          rw [listAppend_singleton, listFoldr_cons,
            mutateSpatialBlockAt_foldr_disjoint bId pTag newCells _
              (fun _ _ _ _ => rfl) hFrame hDisjIds]
          dsimp only
          have hLenEq : (newCells.length == cells.length) = true :=
            natBeqOp_eq_true_of_eq newCells.length cells.length hLen
          have hCond1 : (bId == bId) = true := natBeqOp_refl bId
          have hCond2 :
              (((pTag == pTag &&
                (match SpatialPerm.readWrite with
                 | .readWrite => true
                 | .readOnly => false)) &&
                (0 == 0)) &&
                (newCells.length == cells.length)) = true := by
            rw [natBeqOp_refl pTag, hLenEq]
            rfl
          rw [ite_bool_true hCond1, ite_bool_false rfl, ite_bool_true hCond2]
          rfl
        · intro b1 b2 hb1 hb2
          cases hb1 with
          | head _ =>
            exact hDisj ⟨bId, orig, .readWrite, pTag, 0, cells⟩ b2
              (List.Mem.head []) hb2
          | tail _ hImpossible => cases hImpossible
        · exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

private theorem u32Encode_length_4 (u : Nat) (hLt : Nat.blt u 4294967296 = true) :
    (u32TaggedByteCodec.encode (.scalar ⟨.i32, false, BitVec.ofNat 128 u⟩)).length = 4 := by
  have hNatLt : u < 4294967296 := natLt_of_blt u 4294967296 hLt
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 := by
    exact natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hBvToNat : (BitVec.ofNat 128 u).toNat = u := by
    change Nat.mod u (Nat.pow 2 128) = u
    exact natMod_eq_of_lt (Nat.lt_of_lt_of_le hNatLt hPow128)
  change (u32TaggedEncode (.scalar ⟨.i32, false, BitVec.ofNat 128 u⟩)).length = 4
  dsimp only [u32TaggedEncode]
  rw [hBvToNat, hLt]
  rw [Bool.not_false, Bool.true_and, ite_bool_true rfl, listLength_map]
  exact execEncodeUInt_length execProfileTargetEndian 4 u

private theorem u32Encode_no_uninit (u : Nat) (hLt : Nat.blt u 4294967296 = true) :
    hasUninitCell
      (u32TaggedByteCodec.encode (.scalar ⟨.i32, false, BitVec.ofNat 128 u⟩)) = false := by
  have hNatLt : u < 4294967296 := natLt_of_blt u 4294967296 hLt
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 := natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hBvToNat : (BitVec.ofNat 128 u).toNat = u := by
    change Nat.mod u (Nat.pow 2 128) = u
    exact natMod_eq_of_lt (Nat.lt_of_lt_of_le hNatLt hPow128)
  change hasUninitCell
    (u32TaggedEncode (.scalar ⟨.i32, false, BitVec.ofNat 128 u⟩)) = false
  dsimp only [u32TaggedEncode]
  rw [hBvToNat, hLt, Bool.not_false, Bool.true_and, ite_bool_true rfl]
  exact hasUninitCell_map_rawByte _

private theorem initCellVals_map_rawByte :
    ∀ (bs : List UInt8), initCellVals (bs.map CellVal.rawByte) = ([] : List Val)
  | [] => rfl
  | _ :: rest => initCellVals_map_rawByte rest

private theorem u32Encode_accounted (loans : List (LoanEntry Val)) (v : Val)
    (u : Nat) (hLt : Nat.blt u 4294967296 = true) :
    cellsAccountedByVal mirValAlg loans v
      (u32TaggedByteCodec.encode (.scalar ⟨.i32, false, BitVec.ofNat 128 u⟩)) =
      true := by
  have hNatLt : u < 4294967296 := natLt_of_blt u 4294967296 hLt
  have hPow128 : 4294967296 ≤ Nat.pow 2 128 := natLe_of_ble 4294967296 (Nat.pow 2 128) rfl
  have hBvToNat : (BitVec.ofNat 128 u).toNat = u := by
    change Nat.mod u (Nat.pow 2 128) = u
    exact natMod_eq_of_lt (Nat.lt_of_lt_of_le hNatLt hPow128)
  change cellsAccountedByVal mirValAlg loans v
    (u32TaggedEncode (.scalar ⟨.i32, false, BitVec.ofNat 128 u⟩)) = true
  dsimp only [u32TaggedEncode]
  rw [hBvToNat, hLt, Bool.not_false, Bool.true_and, ite_bool_true rfl]
  dsimp only [cellsAccountedByVal]
  rw [initCellVals_map_rawByte]

/-- End-to-end framed `freezeToSpatialInState` / `mutateSpatialInState` /
`reabsorbFromSpatialInState` lifecycle for `u32TaggedByteCodec`. -/
theorem live_spatialPin_u32_freeze_mutate_reabsorb_frame_sound
    (initU32 newU32 : Nat)
    (hInit : Nat.blt initU32 4294967296 = true)
    (hNew : Nat.blt newU32 4294967296 = true)
    (pureExtra : Nat)
    (frameCells : List (CellVal Val)) :
    let initVal : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 initU32⟩
    let newVal : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 newU32⟩
    let pureVal : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 pureExtra⟩
    let frameBlk : SpatialBlock Val :=
      ⟨9, 9, .readWrite, 9, 0, frameCells⟩
    let st0 : SymState Val :=
      { locals := [⟨initVal, .mutLocked 0⟩, ⟨mirEncodeRef 0 [], .unborrowed⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨initVal, .unborrowed⟩, .direct (.localReg 0) []⟩
          , ⟨2, .activeMut, ⟨pureVal, .unborrowed⟩, .rootParam 2⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := [frameBlk]
        nextSpatialTag := 1 }
    let oldCells := u32TaggedByteCodec.encode initVal
    let newCells := u32TaggedByteCodec.encode newVal
    Exists fun stPinned =>
    Exists fun stMut =>
    Exists fun stReabsorbed =>
    Exists fun stEnd =>
      freezeToSpatialInState mirValAlg 0 u32TaggedByteCodec st0 =
        .ok stPinned ∧
      mutateSpatialInState 1 1 newCells stPinned = .ok stMut ∧
      reabsorbFromSpatialInState mirValAlg 0 u32TaggedByteCodec stMut =
        .ok stReabsorbed ∧
      endLoanInState mirValAlg 0 stReabsorbed = .ok stEnd ∧
      oldCells.length = 4 ∧
      newCells.length = 4 ∧
      stMut.spatial = [frameBlk, ⟨1, 0, .readWrite, 1, 0, newCells⟩] ∧
      findLoan 2 stMut.loans =
        some ⟨2, .activeMut, ⟨pureVal, .unborrowed⟩, .rootParam 2⟩ ∧
      stReabsorbed.spatial = [frameBlk] ∧
      getLocal mirValAlg 0 stEnd = some newVal ∧
      (Exists fun hOut =>
        mutateSpatialBlockAt 1 1 newCells [⟨1, 0, .readWrite, 1, 0, oldCells⟩, frameBlk] =
          some hOut ∧
        spatialSepConj
          (spatialPointsToTagged 1 1 .readWrite newCells)
          (spatialPointsTo 9 .readWrite frameCells)
          hOut) ∧
      (let cInit : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 0x11223344⟩
       let cMut : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 0x11223399⟩
       let cCells : List (CellVal Val) :=
         [.rawByte 0x11, .rawByte 0x22, .rawByte 0x33, .rawByte 0x99]
       u32TaggedByteCodec.encode cInit =
         [.rawByte 0x11, .rawByte 0x22, .rawByte 0x33, .rawByte 0x44] ∧
       u32TaggedByteCodec.decode cCells = some cMut) := by
  intro initVal newVal pureVal frameBlk st0 oldCells newCells
  have hNoUninit : hasUninitCell oldCells = false :=
    u32Encode_no_uninit initU32 hInit
  have hOldLen : oldCells.length = 4 := u32Encode_length_4 initU32 hInit
  have hNewLen : newCells.length = 4 := u32Encode_length_4 newU32 hNew
  have hLenEq : newCells.length = oldCells.length := Eq.trans hNewLen hOldLen.symm
  let blkPinned : SpatialBlock Val :=
    ⟨1, 0, .readWrite, 1, 0, oldCells⟩
  let stPinned : SymState Val :=
    { locals := st0.locals
      loans :=
        [ ⟨0, .spatialPinned 1 u32TaggedByteCodec, ⟨initVal, .unborrowed⟩, .direct (.localReg 0) []⟩
        , ⟨2, .activeMut, ⟨pureVal, .unborrowed⟩, .rootParam 2⟩ ]
      regionGroups := []
      regionDeposits := []
      spatial := [frameBlk, blkPinned]
      nextSpatialTag := 2 }
  let blkMut : SpatialBlock Val :=
    ⟨1, 0, .readWrite, 1, 0, newCells⟩
  let stMut : SymState Val :=
    { stPinned with spatial := [frameBlk, blkMut] }
  let stReabsorbed : SymState Val :=
    { locals := st0.locals
      loans :=
        [ ⟨0, .activeMut, ⟨newVal, .unborrowed⟩, .direct (.localReg 0) []⟩
        , ⟨2, .activeMut, ⟨pureVal, .unborrowed⟩, .rootParam 2⟩ ]
      regionGroups := []
      regionDeposits := []
      spatial := [frameBlk]
      nextSpatialTag := 2 }
  let stEnd : SymState Val :=
    { locals := [⟨newVal, .unborrowed⟩, ⟨mirEncodeRef 0 [], .unborrowed⟩]
      loans :=
        [ ⟨0, .ended, ⟨newVal, .unborrowed⟩, .direct (.localReg 0) []⟩
        , ⟨2, .activeMut, ⟨pureVal, .unborrowed⟩, .rootParam 2⟩ ]
      regionGroups := []
      regionDeposits := []
      spatial := [frameBlk]
      nextSpatialTag := 2 }
  have hFreeze :
      freezeToSpatialInState mirValAlg 0 u32TaggedByteCodec st0 =
        .ok stPinned := by
    have hAcc :
        cellsAccountedByVal mirValAlg st0.loans initVal oldCells = true :=
      u32Encode_accounted st0.loans initVal initU32 hInit
    dsimp only [freezeToSpatialInState]
    change
      (if hasUninitCell oldCells ||
          !cellsAccountedByVal mirValAlg st0.loans initVal oldCells then
         EvalOutcome.fail
       else EvalOutcome.ok stPinned) =
      EvalOutcome.ok stPinned
    rw [hNoUninit, hAcc]
    rfl
  have hMutate :
      mutateSpatialInState 1 1 newCells stPinned = .ok stMut := by
    have hBeqLen : (newCells.length == oldCells.length) = true :=
      natBeqOp_eq_true_of_eq newCells.length oldCells.length hLenEq
    have hCondBlk :
        (((blkPinned.provenanceTag == 1 &&
          (match blkPinned.perm with
           | .readWrite => true
           | .readOnly => false)) &&
          blkPinned.activeSubSplits == 0) &&
          newCells.length == blkPinned.cells.length) = true := by
      dsimp only [blkPinned]
      rw [hBeqLen]
      rfl
    have hBlkId1 : (blkPinned.blockId == 1) = true := rfl
    have hFrmId1 : (frameBlk.blockId == 1) = false := rfl
    dsimp only [mutateSpatialInState, mutateSpatialBlockAt,
      stPinned]
    rw [listFoldr_cons, listFoldr_cons, listFoldr_nil]
    dsimp only
    rw [ite_bool_true hBlkId1, ite_bool_false rfl, ite_bool_true hCondBlk]
    dsimp only
    rw [ite_bool_false hFrmId1]
  have hReabsorb :
      reabsorbFromSpatialInState mirValAlg 0 u32TaggedByteCodec stMut =
        .ok stReabsorbed := by
    have hNoUninitNew : hasUninitCell newCells = false :=
      u32Encode_no_uninit newU32 hNew
    have hDecNew : u32TaggedByteCodec.decode newCells = some newVal :=
      u32TaggedByteCodec_lawful newVal
    have hNotUniq : (!hasUniqueLoanId 0 stMut.loans) = false := rfl
    have hFind :
        findLoan 0 stMut.loans =
          some ⟨0, .spatialPinned 1 u32TaggedByteCodec, ⟨initVal, .unborrowed⟩,
            .direct (.localReg 0) []⟩ := rfl
    have hCidNe : (u32TaggedByteCodec.codecId != u32TaggedByteCodec.codecId) = false := rfl
    have hFindBlk :
        findSpatialBlock stMut.spatial 1 = some (blkMut, [frameBlk]) := rfl
    have hAccNew :
        cellsAccountedByVal mirValAlg stMut.loans initVal newCells = true :=
      u32Encode_accounted stMut.loans initVal newU32 hNew
    have hBlkCheck :
        ((blkMut.originLoan == 0 && blkMut.provenanceTag == 1 &&
            (match blkMut.perm with | .readWrite => true | .readOnly => false)) &&
          countBlocksForLoan 0 [frameBlk] == 0 &&
          blkMut.activeSubSplits == 0 &&
          !hasUninitCell blkMut.cells &&
          cellsAccountedByVal mirValAlg stMut.loans initVal blkMut.cells) = true := by
      dsimp only [blkMut]
      rw [hNoUninitNew, hAccNew]
      rfl
    have hRep :
        (!replaceableVal mirValAlg stMut.loans initVal newVal) =
          false := by
      rfl
    dsimp only [reabsorbFromSpatialInState]
    rw [ite_bool_false hNotUniq, hFind]
    dsimp only
    rw [ite_bool_false hCidNe, hFindBlk]
    dsimp only
    rw [ite_bool_true hBlkCheck]
    dsimp only [blkMut]
    rw [hDecNew]
    dsimp only
    rw [ite_bool_false hRep]
    rfl
  have hEnd :
      endLoanInState mirValAlg 0 stReabsorbed = .ok stEnd := by
    rfl
  have hFrameSep :
      Exists fun hOut =>
        mutateSpatialBlockAt 1 1 newCells [blkPinned, frameBlk] = some hOut ∧
        spatialSepConj
          (spatialPointsToTagged 1 1 .readWrite newCells)
          (spatialPointsTo 9 .readWrite frameCells)
          hOut := by
    refine spatial_frame_law
      (spatialPointsToTagged 1 1 .readWrite oldCells)
      (spatialPointsToTagged 1 1 .readWrite newCells)
      (spatialPointsTo 9 .readWrite frameCells)
      (mutateSpatialBlockAt 1 1 newCells)
      (mutateSpatialBlockAt_pointsTo_triple 1 1 oldCells newCells hLenEq)
      [blkPinned, frameBlk]
      ⟨[blkPinned], [frameBlk], rfl, ?_, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
    intro b1 b2 hb1 hb2
    cases hb1 with
    | tail _ hImp => cases hImp
    | head _ =>
      cases hb2 with
      | tail _ hImp => cases hImp
      | head _ =>
        dsimp only [blkPinned, frameBlk]
        exact ⟨fun hEq => Bool.noConfusion (congrArg (Nat.beq 1) hEq),
               fun hEq => Bool.noConfusion (congrArg (Nat.beq 0) hEq)⟩
  exact ⟨stPinned, stMut, stReabsorbed, stEnd,
    hFreeze, hMutate, hReabsorb, hEnd, hOldLen, hNewLen,
    rfl, rfl, rfl, rfl, hFrameSep, ⟨rfl, rfl⟩⟩

end Anneal.PureLift

end
