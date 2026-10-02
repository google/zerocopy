/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Required
import ContractTests
open Lean Elab Command
run_elab do
  let required := requiredTheorems
  let env ← getEnv
  for declName in required do
    match env.find? declName with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing required theorem {declName}"
  let prefixes := #[`Zerocopy.Proofs, `Zerocopy.Obligations, `Zerocopy.util, `core.num,
                    `AeneasContracts, `ContractTests]
  let mut audited := 0
  for (declName, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName declName)) then
      let used ← collectAxioms declName
      for ax in used do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{declName} depends on unapproved axiom {ax}"
      audited := audited + 1
  logInfo m!"Checked axiom dependencies of {audited} declarations"
