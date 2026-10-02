/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Required
import ContractTests
import SupportTests
import Corollaries
open Lean Elab Command
run_elab do
  let required := requiredTheorems
  let env ← getEnv
  for declName in required do
    match env.find? declName with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing required theorem {declName}"
  let some proofModule := env.getModuleIdxFor? required[0]!
    | throwError "Required proofs must be imported from the generated Proofs module"
  for (declName, declared) in proofDependencies do
    -- Inspect elaborated terms, including compiler-generated local helpers.
    -- Stop at another registered theorem: its own edges are checked separately.
    let mut pending := #[declName]
    let mut visited : NameHashSet := {}
    let mut actual : Array Name := #[]
    while !pending.isEmpty do
      let current := pending.back!
      pending := pending.pop
      if visited.contains current then continue
      visited := visited.insert current
      let some info := env.find? current
        | throwError "Missing proof declaration {current}"
      let references := info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      for used in references do
        if used == declName then continue
        if required.contains used then
          unless actual.contains used do actual := actual.push used
        else if env.getModuleIdxFor? used == some proofModule ||
            (`Zerocopy.Proofs).isPrefixOf (privateToUserName used) then
          pending := pending.push used
    for used in actual do
      unless declared.contains used do
        throwError "{declName} has undeclared proof dependency {used}"
    for used in declared do
      unless actual.contains used do
        throwError "{declName} has unused proof dependency {used}"
  logInfo m!"Checked proof dependencies of {proofDependencies.size} theorems"
  let prefixes := #[`Zerocopy, `core.num, `AeneasContracts, `ContractTests, `SupportTests]
  let mut audited := 0
  let some checksModule := env.getModuleIdxFor? `requiredTheorems
    | throwError "Required contract checks must be imported from their own module"
  for (declName, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName declName)) ||
        env.getModuleIdxFor? declName == some proofModule ||
        env.getModuleIdxFor? declName == some checksModule then
      let used ← collectAxioms declName
      for ax in used do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{declName} depends on unapproved axiom {ax}"
      audited := audited + 1
  logInfo m!"Checked axiom dependencies of {audited} declarations"
