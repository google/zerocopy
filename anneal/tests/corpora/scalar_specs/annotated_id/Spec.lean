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

def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program =>
      ∃ body, program.bodies = [body] ∧
        ∀ bits : BitVec 128,
          truncateBits .isize bits = bits →
          Behavior (entryProgForBody program 0)
            { args := [.scalar ⟨.isize, false, bits⟩] }
            (.returned ⟨.scalar ⟨.isize, false, bits⟩, ⟨[]⟩⟩) }

end Spec
