/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import RustAeneas.Machine
import RustAeneas.Bytes
import Lean.Util.CollectAxioms
import Lean.Elab.Command

example (lay : Rust.Machine.Layout) :
    lay.toSpecLayout.size = lay.size.val := rfl

example (lay : Rust.Machine.SpecLayout) [Rust.Machine.FitsInUsize lay] :
    lay.toLayout.toSpecLayout.size = lay.size := by simp [Rust.Machine.SpecLayout.toLayout,
      Rust.Machine.Layout.toSpecLayout]

-- Keep the Aeneas-backed machine layer separate from the pure Rust audit.
-- Only standard logical axioms are permitted in this companion's declarations.
run_cmd do
  let env ← Lean.getEnv
  let modules := #[`RustAeneas.Machine, `RustAeneas.Bytes]
  let owners ← modules.mapM fun moduleName => do
    let some owner := env.getModuleIdx? moduleName
      | throwError "Companion module was not imported: {moduleName}"
    pure owner
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut audited := 0
  for (name, _) in env.constants.toList do
    if let some owner := env.getModuleIdxFor? name then
      if owners.contains owner then
        for assumption in ← Lean.collectAxioms name do
          unless allowed.contains assumption do
            throwError "Companion declaration {name} depends on forbidden axiom {assumption}"
        audited := audited + 1
  unless audited > 0 do
    throwError "Companion axiom audit found no declarations"
  Lean.logInfo m!"Companion axiom audit checked {audited} declarations"
