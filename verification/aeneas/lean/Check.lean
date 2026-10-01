/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Required
open Lean Elab Command
run_elab do
  let env ← getEnv
  let layoutInputs := #[`Zerocopy.RustLayout.size, `Zerocopy.RustLayout.align]
  -- Generic alignment reads identify the ABI-capable model. Earlier models
  -- may have only the pointer-width size read and require no generic ABI inputs.
  let hasLayoutReads := env.contains `core.mem.align_of
  let modelInputs := if hasLayoutReads then layoutInputs else #[]
  let expected ← Term.elabType (← `(Type → Aeneas.Std.Usize))
  for input in modelInputs do
    let some (.axiomInfo info) := env.find? input
      | throwError "Missing external layout input {input}"
    unless ← Meta.isDefEq info.type expected do
      throwError "External layout input {input} changed its data-only signature"
  if hasLayoutReads then
    -- Independently state each primitive interpretation. Keeping the data
    -- axioms while ignoring them must not silently shrink the modeled domain.
    let alignRead ← Term.elabTerm (← `(
      fun (T : Type) => Aeneas.Std.Result.ok (Zerocopy.RustLayout.align T))) none
    let sizeRead ← Term.elabTerm (← `(
      fun (T : Type) => by
        classical
        exact Aeneas.Std.Result.ok
          (if T = Aeneas.Std.Usize then
            ({ bv := BitVec.ofNat _ (System.Platform.numBits / 8) } : Aeneas.Std.Usize)
           else Zerocopy.RustLayout.size T))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let alignRead ← instantiateMVars alignRead
    let sizeRead ← instantiateMVars sizeRead
    unless ← Meta.isDefEq (mkConst `core.mem.align_of) alignRead do
      throwError "External alignment read changed its data-input interpretation"
    unless env.contains `core.mem.size_of do
      throwError "Missing external size read"
    unless ← Meta.isDefEq (mkConst `core.mem.size_of) sizeRead do
      throwError "External size read changed its data-input interpretation"
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
  -- Compiled spec declarations determine coverage; there is no separately
  -- generated theorem roster that can omit a specification and its checks.
  let some specsModule := env.getModuleIdx? `Specs
    | throwError "Compiled inline specifications must be imported"
  let mut required : Array Name := #[]
  let mut actualModels : Array Name := #[]
  for (declName, info) in env.constants.toList do
    if env.getModuleIdxFor? declName != some specsModule ||
        declName.getPrefix != `Zerocopy.Specs then continue
    let .defnInfo info := info
      | throwError "Unexpected inline specification declaration {declName}"
    unless info.type.consumeMData == mkSort Level.zero do
      throwError "Inline specification {declName} must be a proposition"
    let (modelName, _) ← AeneasSpecs.specBinding declName
    if actualModels.contains modelName then
      throwError "Compiled inline specifications repeat model {modelName}"
    actualModels := actualModels.push modelName
    required := required.push ((`Zerocopy.Proofs).str declName.getString!)
  if required.isEmpty then
    throwError "No compiled inline specifications were found"
  -- Reuse the model mapping already produced from Rust annotations/extraction.
  -- Deriving both Specs and Required from a smaller subset cannot hide a root.
  let bindingsText ← IO.FS.readFile "bindings.json"
  let .ok bindings := Json.parse bindingsText
    | throwError "Model bindings are not valid JSON"
  let .ok version := bindings.getObjValAs? Nat "version"
    | throwError "Model bindings must declare version 2"
  unless version == 2 do
    throwError "Model bindings must declare version 2"
  let .ok mode := bindings.getObjValAs? String "mode"
    | throwError "Model bindings must declare their validation mode"
  unless mode == "verified-live" || mode == "development" do
    throwError "Model bindings have an unsupported validation mode {mode}"
  let .ok modelValues := bindings.getObjVal? "models"
    | throwError "Model bindings must contain their model mapping"
  let .ok models := modelValues.getObj?
    | throwError "Model bindings must contain a model mapping object"
  let .ok invariantValues := bindings.getObjVal? "invariants"
    | throwError "Model bindings must contain their invariant mapping"
  let .ok invariants := invariantValues.getObj?
    | throwError "Model bindings must contain an invariant mapping object"
  let some invariantModule := env.getModuleIdx? `Invariants
    | throwError "Invariants must be imported from their generated module"
  -- Unannotated parents carry their children's validity too. Audit the already
  -- verified extracted type image so an omitted derivation cannot select True.
  let .ok extractedTypes := bindings.getObjValAs? (Array Json) "types"
    | throwError "Model bindings must contain their extracted type image"
  let mut expectedInstances : Array Name := #[]
  for entry in extractedTypes do
    let .ok model := entry.getObjValAs? String "model"
      | throwError "Extracted type binding must name its model carrier"
    let .ok generics := entry.getObjValAs? (Array String) "generics"
      | throwError "Extracted type binding must name its original type parameters"
    let carrier := (`Zerocopy).append model.toName
    let instanceName := carrier ++ `aeneasValid
    if expectedInstances.contains instanceName then
      throwError "Extracted type bindings repeat carrier {carrier}"
    expectedInstances := expectedInstances.push instanceName
    let some (.inductInfo typeInfo) := env.find? carrier
      | throwError "Extracted type binding is not a nominal model: {carrier}"
    unless typeInfo.numParams == generics.size do
      throwError "Extracted type binding changed its type parameters: {carrier}"
    let some (.defnInfo instanceInfo) := env.find? instanceName
      | throwError "Missing structural validity instance for extracted model {carrier}"
    unless env.getModuleIdxFor? instanceName == some invariantModule &&
        (← Meta.isInstance instanceName) do
      throwError "Structural validity must be registered by Invariants: {carrier}"
    Meta.forallTelescope instanceInfo.type fun inputs target => do
      unless inputs.size == 2 * generics.size do
        throwError "Structural validity has an unexpected telescope: {carrier}"
      let originals := inputs.extract 0 generics.size
      for i in [:generics.size] do
        let dictionaryType ← Meta.mkAppM ``AeneasSpecs.IsValid #[originals[i]!]
        unless ← Meta.isDefEq (← Meta.inferType inputs[generics.size + i]!) dictionaryType do
          throwError "Structural validity changed its generic dictionary: {carrier}"
      let modelType := mkAppN (mkConst carrier (typeInfo.levelParams.map Level.param)) originals
      unless ← Meta.isDefEq target (← Meta.mkAppM ``AeneasSpecs.IsValid #[modelType]) do
        throwError "Structural validity has an unexpected carrier: {carrier}"
  let actualInstances := (← AeneasSpecs.canonicalValidityProviders).filter
    (fun instanceName => env.getModuleIdxFor? instanceName == some invariantModule)
  let missingInstances := expectedInstances.filter (!actualInstances.contains ·)
  let extraInstances := actualInstances.filter (!expectedInstances.contains ·)
  unless missingInstances.isEmpty && extraInstances.isEmpty do
    throwError "Structural validity disagrees with extracted type bindings: missing {missingInstances}; unexpected {extraInstances}"
  let actualInvariants := (← AeneasSpecs.authoredInvariantNames).filter
    (fun predicate => env.getModuleIdxFor? predicate == some invariantModule)
  let mut expectedInvariants : Array Name := #[]
  for (rustName, value) in invariants.toArray do
    let .ok predicate := value.getStr?
      | throwError "Invariant binding for {rustName} must be a string"
    let .ok carrier := modelValues.getObjValAs? String rustName
      | throwError "Invariant binding for {rustName} lacks its model carrier"
    let predicateName := (`Zerocopy.Invariants).append predicate.toName
    if expectedInvariants.contains predicateName then
      throwError "Invariant bindings repeat predicate {predicateName}"
    expectedInvariants := expectedInvariants.push predicateName
    let (actualCarrier, _, _) ← AeneasSpecs.invariantBinding predicateName
    unless actualCarrier == (`Zerocopy).append carrier.toName do
      throwError "Compiled invariant {predicateName} disagrees with its Rust model binding"
  let missingInvariants := expectedInvariants.filter (!actualInvariants.contains ·)
  let extraInvariants := actualInvariants.filter (!expectedInvariants.contains ·)
  unless missingInvariants.isEmpty && extraInvariants.isEmpty do
    throwError "Compiled inline invariants disagree with bindings: missing {missingInvariants}; unexpected {extraInvariants}"
  let mut expectedModels : Array Name := #[]
  for (rustName, value) in models.toArray do
    if (invariantValues.getObjVal? rustName).isOk then continue
    let .ok model := value.getStr?
      | throwError "Model binding for {rustName} must be a string"
    -- The producer validates generated-name syntax. Compare the actual typed
    -- declaration identity here instead of maintaining a second character lexer.
    let modelName := (`Zerocopy).append model.toName
    if expectedModels.contains modelName then
      throwError "Model bindings repeat model {modelName}"
    expectedModels := expectedModels.push modelName
  let missing := expectedModels.filter (fun model => !actualModels.contains model)
  let extra := actualModels.filter (fun model => !expectedModels.contains model)
  unless missing.isEmpty && extra.isEmpty do
    throwError "Compiled inline specification models disagree with bindings: missing {missing}; unexpected {extra}"
  required := required.qsort (fun a b => a.toString < b.toString)
  let some checksModule := env.getModuleIdx? `Required
    | throwError "Required checks must be imported from their own module"
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
    let obligationName := (`Zerocopy.Obligations).str declName.getString!
    let witnessName := obligationName.appendAfter "_checked"
    let some (.thmInfo witness) := env.find? witnessName
      | throwError "Missing independent required theorem {witnessName}"
    unless ← Meta.isDefEq witness.type (mkConst obligationName) do
      throwError "{witnessName} does not prove its independent required proposition"
    unless env.getModuleIdxFor? witnessName == some checksModule do
      throwError "{witnessName} must be declared in the required checks module"
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
