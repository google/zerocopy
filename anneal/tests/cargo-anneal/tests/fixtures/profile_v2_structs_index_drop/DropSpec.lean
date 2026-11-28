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

/-- `first::<u8>` returns its first argument; its no-drop-glue `drop(_2)`
leaves the caller-visible memory unchanged. -/
def firstPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [x, _] =>
        BehaviorV2 (entryProgForBody p 0) q
          (TerminalOut.returned ⟨x, q.callerMem⟩)
      | _ => False

def specs : SpecsV2 := ⟨fun _ _ => True, firstPost⟩

end Spec
