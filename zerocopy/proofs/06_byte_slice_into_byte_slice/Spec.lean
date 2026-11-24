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

/-- All three `into_byte_slice{,_mut}` bodies are safe functions, so the
safety precondition is never consulted by `BodyVerifiedV2`. -/
def safetyPre (_identity : String) (_q : Query) : Prop := True

/-- Stability: on every valid entry `q` whose sole argument is the byte slice
`(ptr, len)`, the body is well-formed, it returns a slice with the same
address and length while leaving caller memory unchanged, and that is its
only terminal behavior. -/
def stableBodyPost (p : Program) (defId : DefId) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.slicePtr ptr len] =>
        let out := TerminalOut.returned ⟨.slicePtr ptr len, q.callerMem⟩
        BehaviorV2 (entryProgForBody p defId) q out ∧
        SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)
      | _ => False

/-- Body 0: `<&[u8] as IntoByteSlice>::into_byte_slice`.
Body 1: `<&mut [u8] as IntoByteSlice>::into_byte_slice`.
Body 2: `<&mut [u8] as IntoByteSliceMut>::into_byte_slice_mut`. -/
def property (p : Program) : Prop :=
  stableBodyPost p 0 ∧ stableBodyPost p 1 ∧ stableBodyPost p 2

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
