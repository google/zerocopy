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

def splitAtSharedIdentity : String :=
  "rust-path-v1::<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"

def splitAtSafety (q : Query) : Prop :=
  match q.args with
  | [.slicePtr _ len, .scalar mid] => mid.bits.toNat ≤ len.toNat
  | _ => False

def safetyPre (identity : String) (q : Query) : Prop :=
  if identity = splitAtSharedIdentity then splitAtSafety q else False

def splitAtBodyPost (p : Program) (defId : DefId) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      splitAtSafety q →
      match q.args with
      | [.slicePtr ptr len, .scalar mid] =>
        let pR :=
          match ptr.allocId with
          | none => ptr
          | some _ =>
            { ptr with
              offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + mid.bits.toNat) }
        let lenL := UInt64.ofNat mid.bits.toNat
        let lenR := UInt64.ofNat (len.toNat - mid.bits.toNat)
        ∃ out : TerminalOut,
          BehaviorV2 (entryProgForBody p defId) q out ∧
          out = TerminalOut.returned
            ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩ ∧
          lenL.toNat + lenR.toNat = len.toNat
      | _ => False

def property (p : Program) : Prop :=
  splitAtBodyPost p 0

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
