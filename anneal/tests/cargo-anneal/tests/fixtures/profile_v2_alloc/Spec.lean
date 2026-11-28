-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def vecAndBoxSliceIdentity : String := "rust-path-v1::vec_and_box_slice"

def boxNewDerefIdentity : String := "rust-path-v1::box_new_and_deref"

def vecWithCapIdentity : String := "rust-path-v1::vec_with_cap_arg"

def readSliceBoxLenIdentity : String :=
  "rust-path-v1::read_slice_and_box_len"

def pushOneIdentity : String := "rust-path-v1::push_one"

def vecWithCapSafety (q : Query) : Prop :=
  match q.args with
  | [.scalar capSv] => capSv.bits.toNat < isizeMaxBytes
  | _ => False

/-- `push_one`'s caller obligation: growing the `Vec<u8>` behind the argument
cannot overflow `isize::MAX` bytes, so `push` cannot panic. -/
def pushOneSafety (q : Query) : Prop :=
  match q.args with
  | [.ptr selfPtr] =>
    ∀ v : VecModel,
      readVecFromRef (entryMemoryWithCaller q.callerMem) true
        (.int .i8 false) selfPtr = .ok v →
      v.cap.toNat * 2 < isizeMaxBytes
  | _ => False

def safetyPre (identity : String) (q : Query) : Prop :=
  if identity = vecAndBoxSliceIdentity then True
  else if identity = boxNewDerefIdentity then True
  else if identity = vecWithCapIdentity then vecWithCapSafety q
  else if identity = readSliceBoxLenIdentity then True
  else if identity = pushOneIdentity then pushOneSafety q
  else False

/-- `vec_and_box_slice` returns `src`, `b`, and `c`, whose heap buffers are
fresh allocations, in that order, appended to the caller's memory and holding
exactly `[9]`, `[10, 9]`, and `[10, 9]`. -/
def vecAndBoxSlicePost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      ∃ (sId bId cId : AllocId),
        (∀ a : Allocation, a ∈ q.callerMem.allocations → a.allocId < sId) ∧
        sId < bId ∧ bId < cId ∧
        BehaviorV2 (entryProgForBody p 0) q
          (TerminalOut.returned
            ⟨.tuple
              [ .scalar
                  ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
              , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
              , .vec ⟨some sId, 0, .isize⟩ 1 1
              , .boxPtr ⟨some bId, 0, .isize⟩ (some 2)
              , .boxPtr ⟨some cId, 0, .isize⟩ (some 2)
              ],
              ⟨q.callerMem.allocations ++
                [ ⟨sId, 0, .mut, [.init 9 none], true⟩
                , ⟨bId, 0, .mut, [.init 10 none, .init 9 none], true⟩
                , ⟨cId, 0, .mut, [.init 10 none, .init 9 none], true⟩
                ]⟩⟩)

/-- `box_new_and_deref` returns `0x1234` and a box whose fresh 8-byte heap
buffer, appended to the caller's memory, holds `0x1234` in little-endian
order. -/
def boxNewDerefPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 1 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      ∃ (bId : AllocId),
        (∀ a : Allocation, a ∈ q.callerMem.allocations → a.allocId < bId) ∧
        BehaviorV2 (entryProgForBody p 1) q
          (TerminalOut.returned
            ⟨.tuple
              [ .scalar
                  ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 0x1234)⟩
              , .boxPtr ⟨some bId, 0, .isize⟩ none
              ],
              ⟨q.callerMem.allocations ++
                [ ⟨bId, 3, .mut,
                    [ .init 0x34 none, .init 0x12 none, .init 0 none
                    , .init 0 none, .init 0 none, .init 0 none
                    , .init 0 none, .init 0 none ], true⟩ ]⟩⟩)

def vecWithCapPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 2 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      vecWithCapSafety q →
      WellFormedV2 (entryProgForBody p 2) q

def readSliceBoxLenPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 3 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.slicePtr _ sLen, .ptr bPtr] =>
        ∃ (bPtrOut : PtrVal) (bLen : UInt64),
          readBoxFromRef (entryMemoryWithCaller q.callerMem) false
            (.slice (.int .i8 false)) bPtr =
            .ok ⟨.slice (.int .i8 false), bPtrOut, some bLen⟩ ∧
          WellFormedV2 (entryProgForBody p 3) q ∧
          BehaviorV2 (entryProgForBody p 3) q
            (TerminalOut.returned
              ⟨.tuple
                [ .scalar
                    ⟨.isize, false,
                      truncateBits .isize (BitVec.ofNat 128 sLen.toNat)⟩
                , .scalar
                    ⟨.isize, false,
                      truncateBits .isize (BitVec.ofNat 128 bLen.toNat)⟩
                ], q.callerMem⟩)
      | _ => False

/-- `push_one` never faults, and on every normal return the `Vec<u8>` read back
through the same `&mut` argument has one more element; its buffer starts with
the old elements followed by `1`. This covers both the in-place and the
growing `push`. -/
def pushOnePost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 4 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      pushOneSafety q →
      WellFormedV2 (entryProgForBody p 4) q ∧
      ∀ (out : Out),
        BehaviorV2 (entryProgForBody p 4) q (TerminalOut.returned out) →
        match q.args with
        | [.ptr selfPtr] =>
          ∀ (v : VecModel) (aid : AllocId) (old : List AllocByte),
            readVecFromRef (entryMemoryWithCaller q.callerMem) true
              (.int .i8 false) selfPtr = .ok v →
            (v.len.toNat = 0 ∨ v.ptr.allocId = some aid) →
            readBytes (entryMemoryWithCaller q.callerMem)
              ⟨aid, v.ptr.offsetBytes.toNat⟩ v.len.toNat 0 = .ok old →
            ∃ (v' : VecModel) (aid' : AllocId),
              readVecFromRef (entryMemoryWithCaller out.callerMem) true
                (.int .i8 false) selfPtr = .ok v' ∧
              v'.len.toNat = v.len.toNat + 1 ∧
              v'.ptr.allocId = some aid' ∧
              readBytes (entryMemoryWithCaller out.callerMem)
                ⟨aid', v'.ptr.offsetBytes.toNat⟩ (v.len.toNat + 1) 0 =
                .ok (old ++ [.init 1 none])
        | _ => False

def property (p : Program) : Prop :=
  vecAndBoxSlicePost p ∧ boxNewDerefPost p ∧
  vecWithCapPost p ∧ readSliceBoxLenPost p ∧ pushOnePost p

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
