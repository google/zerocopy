-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace ExecutionSpec

open Trusted.MirAst Trusted.MirSemantics

/--
Every valid entry has an actual source return, without prescribing its value.
-/
noncomputable def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program => ∃ body, program.bodies = [body] ∧
      ∀ args, ValidEntryArgs body args →
        ∃ output,
          Behavior (entryProgForBody program 0) { args := args }
            (.returned ⟨output, ⟨[]⟩⟩) }

end ExecutionSpec
