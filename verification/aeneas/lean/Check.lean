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
  -- Model-support import closure is audited from compiled module identities.
  let mut pendingSupport := env.header.moduleNames.filter ((`ModelSupport).isPrefixOf ·)
  let mut seenSupport : NameHashSet := {}
  while !pendingSupport.isEmpty do
    let moduleName := pendingSupport.back!
    pendingSupport := pendingSupport.pop
    if seenSupport.contains moduleName then continue
    seenSupport := seenSupport.insert moduleName
    if #[`Models, `Specs, `Invariants, `Zerocopy.Funs, `Zerocopy.FunsExternal].contains moduleName ||
        (`Proofs).isPrefixOf moduleName then
      throwError "ModelSupport cannot depend on decoder, specification, proof, or extracted function module: {moduleName}"
    let some index := env.getModuleIdx? moduleName
      | throwError "Missing compiled support dependency module {moduleName}"
    let some moduleData := env.header.moduleData[index]?
      | throwError "Missing compiled import data for support dependency {moduleName}"
    for dependency in moduleData.imports do
      pendingSupport := pendingSupport.push dependency.module
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
    | throwError "Model bindings must declare version 3"
  unless version == 3 do
    throwError "Model bindings must declare version 3"
  let .ok mode := bindings.getObjValAs? String "mode"
    | throwError "Model bindings must declare their validation mode"
  unless mode == "verified-live" || mode == "development" do
    throwError "Model bindings have an unsupported validation mode {mode}"
  let .ok entriesValue := bindings.getObjVal? "bindings"
    | throwError "Model bindings must contain their source/extraction binding table"
  let .ok entries := entriesValue.getObj?
    | throwError "Model bindings must contain a binding table object"
  let some typesModule := env.getModuleIdx? `Zerocopy.Types
    | throwError "Raw extracted types must be imported"
  let some shapesModule := env.getModuleIdx? `ModelShapes
    | throwError "ModelShapes must be imported from their generated module"
  let some modelsModule := env.getModuleIdx? `Models
    | throwError "Models must be imported from their generated module"
  let mut expectedTypes : Array Name := #[]
  let mut expectedModels : Array Name := #[]
  for (rustName, entry) in entries.toArray do
    let .ok kind := entry.getObjValAs? String "kind"
      | throwError "Binding for {rustName} must name its owner kind"
    let .ok raw := entry.getObjValAs? String "raw"
      | throwError "Binding for {rustName} must name its exact extracted carrier"
    let .ok generics := entry.getObjValAs? (Array String) "generics"
      | throwError "Binding for {rustName} must name its original type parameters"
    let rawName := raw.toName
    if kind == "function" then
      if expectedModels.contains rawName then
        throwError "Model bindings repeat model {rawName}"
      expectedModels := expectedModels.push rawName
    else if kind == "type" then
      if expectedTypes.contains rawName then
        throwError "Type bindings repeat extracted carrier {rawName}"
      expectedTypes := expectedTypes.push rawName
      let some (.inductInfo rawInfo) := env.find? rawName
        | throwError "Type binding is not a raw nominal carrier: {rawName}"
      unless env.getModuleIdxFor? rawName == some typesModule &&
          rawInfo.numParams == generics.size do
        throwError "Raw nominal binding changed its ownership or type parameters: {rawName}"
      let (fields, mathType, decoder, provider, count) ← AeneasSpecs.modelBinding rawName
      unless count == generics.size do
        throwError "Mathematical model changed its original generic parameters: {rawName}"
      for (key, actual) in #[("fields", fields), ("model", mathType),
          ("decoder", decoder), ("provider", provider)] do
        let .ok expected := entry.getObjValAs? String key
          | throwError "Type binding for {rustName} must name its {key}"
        unless actual == expected.toName do
          throwError "Compiled {key} {actual} disagrees with its Rust owner binding {expected}"
      unless env.getModuleIdxFor? fields == some shapesModule &&
          env.getModuleIdxFor? mathType == some shapesModule do
        throwError "Mathematical fields and model must be owned by ModelShapes: {rawName}"
      unless env.getModuleIdxFor? decoder == some modelsModule &&
          env.getModuleIdxFor? provider == some modelsModule do
        throwError "Decoder and provider must be owned by Models: {rawName}"
      let .ok authored := entry.getObjValAs? Bool "authored"
        | throwError "Type binding must record its authored model disposition"
      unless authored || mathType == fields do
        throwError "Unannotated model must use its nominal Fields carrier: {rawName}"
    else
      throwError "Unsupported binding kind {kind} for {rustName}"
  -- Independently inspect the complete compiled raw type image. Removing both
  -- a derivation and its manifest entry cannot hide an extracted nominal owner.
  let traitCarriers := (Aeneas.Extract.rustTraitDecls.ext.getState env).filterMap
    fun (_, _, info) => info.extract.map String.toName
  let mut actualTypes : Array Name := #[]
  for (constName, constInfo) in env.constants.toList do
    if (`Zerocopy).isPrefixOf constName && env.getModuleIdxFor? constName == some typesModule &&
        !traitCarriers.any (fun carrier => constName == carrier || constName == (`Zerocopy).append carrier) then
      if let .inductInfo _ := constInfo then
        actualTypes := actualTypes.push constName
  let missingTypes := actualTypes.filter (!expectedTypes.contains ·)
  let extraTypes := expectedTypes.filter (!actualTypes.contains ·)
  unless missingTypes.isEmpty && extraTypes.isEmpty do
    throwError "Raw nominal types disagree with source bindings: missing {missingTypes}; unexpected {extraTypes}"
  let actualOwners := (← AeneasSpecs.modelOwnerNames).filter
    (fun owner => env.getModuleIdxFor? (owner ++ `aeneasModel) == some modelsModule)
  let missingOwners := expectedTypes.filter (!actualOwners.contains ·)
  let extraOwners := actualOwners.filter (!expectedTypes.contains ·)
  unless missingOwners.isEmpty && extraOwners.isEmpty do
    throwError "Compiled mathematical models disagree with bindings: missing {missingOwners}; unexpected {extraOwners}"
  let missing := expectedModels.filter (fun modelName => !actualModels.contains modelName)
  let extra := actualModels.filter (fun modelName => !expectedModels.contains modelName)
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
