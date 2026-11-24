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

def packLeRevIdentity : String :=
  "rust-path-v1::pack_le_rev"

def repeatUnsizeLenIdentity : String :=
  "rust-path-v1::repeat_unsize_len"

def tagEqIdentity : String :=
  "rust-path-v1::tag_eq"

def matchesPatternIdentity : String :=
  "rust-path-v1::matches_pattern"

def safetyPre (identity : String) (_q : Query) : Prop :=
  if identity = packLeRevIdentity then True
  else if identity = repeatUnsizeLenIdentity then True
  else if identity = tagEqIdentity then True
  else if identity = matchesPatternIdentity then True
  else False

noncomputable def readCallerInitByte (cm : CallerMemory) (ptr : PtrVal) : Option UInt8 :=
  match ptr.allocId with
  | none => none
  | some allocId =>
    match findAllocation allocId cm.allocations with
    | none => none
    | some alloc =>
      match Trusted.MirSemantics.getElem? alloc.bytes ptr.offsetBytes.toNat with
      | some (.init b _) => some b
      | _ => none

noncomputable def readCallerFourInitBytes (cm : CallerMemory) (ptr : PtrVal) :
    Option (UInt8 × UInt8 × UInt8 × UInt8) :=
  match ptr.allocId with
  | none => none
  | some allocId =>
    match findAllocation allocId cm.allocations with
    | none => none
    | some alloc =>
      let off := ptr.offsetBytes.toNat
      match Trusted.MirSemantics.getElem? alloc.bytes off,
            Trusted.MirSemantics.getElem? alloc.bytes (off + 1),
            Trusted.MirSemantics.getElem? alloc.bytes (off + 2),
            Trusted.MirSemantics.getElem? alloc.bytes (off + 3) with
      | some (.init b0 _), some (.init b1 _), some (.init b2 _), some (.init b3 _) =>
        some (b0, b1, b2, b3)
      | _, _, _, _ => none

def packLeRevBodyPost (p : Program) (defId : DefId) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.scalar x] =>
        let lo := BitVec.ofNat 128 (x.bits.toNat % 256)
        let hi := BitVec.ofNat 128 ((x.bits.toNat / 256) % 256)
        ∃ out : TerminalOut,
          BehaviorV2 (entryProgForBody p defId) q out ∧
          out = TerminalOut.returned
            ⟨.array [.scalar ⟨.i8, false, hi⟩, .scalar ⟨.i8, false, lo⟩], q.callerMem⟩
      | _ => False

def repeatUnsizeLenBodyPost (p : Program) (defId : DefId) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      ∃ out : TerminalOut,
        BehaviorV2 (entryProgForBody p defId) q out ∧
        out = TerminalOut.returned
          ⟨.scalar ⟨.isize, false, BitVec.ofNat 128 3⟩, q.callerMem⟩

def tagEqBodyPost (p : Program) (defId : DefId) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.ptr pa, .ptr pb] =>
        ∃ ba bb : UInt8,
          readCallerInitByte q.callerMem pa = some ba ∧
          readCallerInitByte q.callerMem pb = some bb ∧
          ∃ out : TerminalOut,
            BehaviorV2 (entryProgForBody p defId) q out ∧
            out = TerminalOut.returned ⟨.bool (Nat.beq ba.toNat bb.toNat), q.callerMem⟩
      | _ => False

def matchesPatternBodyPost (p : Program) (defId : DefId) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.ptr pa] =>
        ∃ b0 b1 b2 b3 : UInt8,
          readCallerFourInitBytes q.callerMem pa = some (b0, b1, b2, b3) ∧
          ∃ out : TerminalOut,
            BehaviorV2 (entryProgForBody p defId) q out ∧
            out = TerminalOut.returned
              ⟨.bool (Nat.beq b0.toNat 1 && Nat.beq b1.toNat 2 &&
                      Nat.beq b2.toNat 3 && Nat.beq b3.toNat 4),
               q.callerMem⟩
      | _ => False

def property (p : Program) : Prop :=
  packLeRevBodyPost p 0 ∧
  repeatUnsizeLenBodyPost p 1 ∧
  tagEqBodyPost p 2 ∧
  matchesPatternBodyPost p 3

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
