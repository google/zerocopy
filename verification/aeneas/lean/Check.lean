/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Required
import SpecsSyntaxTests
import ContractTests
import Corollaries
open Lean Elab Command
run_elab do
  let required := requiredTheorems
  let env ← getEnv
  let layoutInputs := #[`Zerocopy.RustLayout.size, `Zerocopy.RustLayout.align]
  let modelInputs := if layoutInputs.any env.contains then layoutInputs else #[]
  let expected ← Term.elabType (← `(Type → Aeneas.Std.Usize))
  for input in modelInputs do
    let some (.axiomInfo info) := env.find? input
      | throwError "Missing external layout input {input}"
    unless ← Meta.isDefEq info.type expected do
      throwError "External layout input {input} changed its data-only signature"
  let mut proofModules : Array ModuleIdx := #[]
  for moduleName in proofModuleNames do
    let some index := env.getModuleIdx? moduleName
      | throwError "Proof module {moduleName} was not imported"
    proofModules := proofModules.push index
  let mut auditModules : Array ModuleIdx := #[]
  for moduleName in auditModuleNames do
    let some index := env.getModuleIdx? moduleName
      | throwError "Audit module {moduleName} was not imported"
    auditModules := auditModules.push index
  for declName in required do
    let some (.thmInfo info) := env.find? declName
      | throwError "Missing required theorem {declName}"
    let specName := (`Zerocopy.Specs).str declName.getString!
    unless env.contains specName do
      throwError "Missing inline specification {specName}"
    unless ← Meta.isDefEq info.type (mkConst specName) do
      throwError "{declName} does not prove its inline specification {specName}"
    unless (env.getModuleIdxFor? declName).any proofModules.contains do
      throwError "{declName} must be declared in a configured proof module"
  let mut graph : Array Json := #[]
  for declName in required do
    -- Follow helpers in every audited handwritten and model module, including
    -- private and generated declarations. Stop at registered callees, whose
    -- own edges follow. Canonical proof ownership remains restricted above.
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
        else if (env.getModuleIdxFor? used).any auditModules.contains then
          pending := pending.push used
    actual := actual.qsort (fun a b => a.toString < b.toString)
    graph := graph.push (Json.mkObj [
      ("theorem", Json.str declName.toString),
      ("depends_on", Json.arr (actual.map (Json.str ∘ Name.toString)))])
  logInfo m!"Recorded proof dependencies of {required.size} theorems"
  let prefixes := #[`Zerocopy, `core.num, `AeneasContracts, `AeneasSpecs,
    `ContractTests, `SpecsSyntaxTests, `SupportTests]
  let mut audited := 0
  let some checksModule := env.getModuleIdxFor? `requiredTheorems
    | throwError "Required checks must be imported from their own module"
  for (declName, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName declName)) ||
        (env.getModuleIdxFor? declName).any auditModules.contains ||
        env.getModuleIdxFor? declName == some checksModule then
      let used ← collectAxioms declName
      for ax in used do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax ||
            modelInputs.contains ax do
          throwError "{declName} depends on unapproved axiom {ax}"
      audited := audited + 1
  IO.FS.writeFile "proof-dependencies.json" (Json.arr graph).pretty
  logInfo m!"Checked axiom dependencies of {audited} declarations"
