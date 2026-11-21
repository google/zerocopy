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

def expectedReturn : TerminalOut :=
  .returned ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩

noncomputable def returnsZero (program : Program) : Prop :=
  let entry := entryProgForBody program 0
  let call : Query := { args := [] }
  SatisfiesPost entry call (fun outcome => outcome = expectedReturn) ∧
    (¬ Diverges entry call) ∧ Behavior entry call expectedReturn

noncomputable def specs : Specs := ⟨fun _ _ => True, returnsZero⟩

end Spec
