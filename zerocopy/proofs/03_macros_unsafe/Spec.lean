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

def unsafeId : String :=
  "rust-path-v1::util::macros::__unsafe"

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous caller safety precondition for `pub(crate) const unsafe fn
__unsafe() {}` (`util/macros.rs`). Callers invoke the exact canonical item
`util::macros::__unsafe` with zero value arguments (`args = []`) and empty
caller memory (`callerMem := ⟨[]⟩`). -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity = unsafeId ∧ args = []

/-- Functional specification for `util::macros::__unsafe`:
1. Single-body unit strictly containing `rust-path-v1::util::macros::__unsafe`;
2. `body.isUnsafe = true` and `body.argumentCount = 0` (preserving the
   compile-time `unsafe { ... }` fence required by macro callers);
3. Calling `__unsafe()` with `[]` terminates cleanly (`¬ Diverges`), faults
   never (`SatisfiesPost`), and returns `()`. -/
noncomputable def macrosUnsafeSpec (program : Program) : Prop :=
  program.bodies.length = 1 ∧
  ∃ defU bodyU,
    getElem? program.bodies defU = some bodyU ∧
    bodyU.identity = unsafeId ∧
    bodyU.isUnsafe = true ∧
    bodyU.argumentCount = 0 ∧
    ReturnsTotal program defU [] .unit

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, macrosUnsafeSpec⟩

end Spec
