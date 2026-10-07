/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Required
open Lean Elab Command

/-!
This is the final compiled audit of the connection from Rust annotations to
Lean proofs. It compares three sources of evidence: the source/extraction
binding manifest, the actual compiled raw types and specifications, and the
configured proof and required-check modules. Each comparison is closed: both
missing and unexpected owners are errors. Deleting an annotation and its proof
together must not erase a promised root from the audit.

After checking ownership and arbitrary-outcome adequacy, the audit records the
proof dependency graph and checks the axioms used by every audited declaration.
The graph reports what the compiled proofs use; it does not prescribe their
structure. External ABI size and alignment inputs are permitted only with their
data signatures and explicit read interpretations, rather than as axioms about
useful layout properties.
-/

run_elab do
  let env ← getEnv
  let layoutInputs := #[`Zerocopy.RustLayout.size, `Zerocopy.RustLayout.align]
  -- Generic alignment reads identify the ABI-capable model. Earlier models
  -- may have only the pointer-width size read and require no generic ABI inputs.
  let hasLayoutReads := env.contains `core.mem.align_of
  let modelInputs := if hasLayoutReads then layoutInputs else #[]
  -- ByteOrder carries formatting dictionaries even when a numerical method
  -- never formats a value. The backend leaves Formatter's representation
  -- abstract. Admit this exact opaque type, with no axiom about its values or
  -- behavior; changing it into a proposition or a function is an error.
  let opaqueCarriers := #[`Aeneas.Std.core.fmt.Formatter]
  let expectedCarrier ← Term.elabType (← `(Type))
  for carrier in opaqueCarriers do
    let some (.axiomInfo info) := env.find? carrier
      | throwError "Missing pinned opaque carrier {carrier}"
    unless info.levelParams.isEmpty && (← Meta.isDefEq info.type expectedCarrier) do
      throwError "Opaque carrier {carrier} changed its type-only signature"
  -- ABI inputs are functions returning data, with no proposition asserting
  -- alignment, size, or correctness. A changed type could smuggle a theorem
  -- into the allowed axiom list, so check their exact compiled signatures.
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
  -- Module indices identify declarations by compiled ownership. A matching
  -- namespace is insufficient: a generated or unrelated module could otherwise
  -- install a theorem under a handwritten proof's expected name.
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
  let mut actualFamilies : Array Name := #[]
  let mut expectedFamilies : Array Name := #[]
  for (declName, info) in env.constants.toList do
    if env.getModuleIdxFor? declName != some specsModule ||
        declName.getPrefix != `Zerocopy.Specs then continue
    let .defnInfo info := info
      | throwError "Unexpected inline specification declaration {declName}"
    -- The generated namespace contains specs and their outcome families only.
    -- Collect untagged definitions for an exact family comparison below, rather
    -- than treating every nearby declaration as an authored contract.
    if !AeneasSpecs.specAttribute.hasTag env declName then
      actualFamilies := actualFamilies.push declName
      continue
    unless info.type.consumeMData == mkSort Level.zero do
      throwError "Inline specification {declName} must be a proposition"
    let (modelName, _) ← AeneasSpecs.specBinding declName
    AeneasSpecs.checkSpecContract declName
    let familyName := AeneasSpecs.specContractName declName
    unless env.getModuleIdxFor? familyName == some specsModule do
      throwError "Abstract contract {familyName} must be declared with its inline specification"
    expectedFamilies := expectedFamilies.push familyName
    -- One Rust function owns one inline specification. Multiple specs could
    -- let the canonical theorem prove a weaker sibling of the intended claim.
    if actualModels.contains modelName then
      throwError "Compiled inline specifications repeat model {modelName}"
    actualModels := actualModels.push modelName
    required := required.push ((`Zerocopy.Proofs).str declName.getString!)
  let missingFamilies := expectedFamilies.filter (!actualFamilies.contains ·)
  let extraFamilies := actualFamilies.filter (!expectedFamilies.contains ·)
  unless missingFamilies.isEmpty && extraFamilies.isEmpty do
    throwError "Compiled abstract contracts disagree with inline specifications: missing {missingFamilies}; unexpected {extraFamilies}"
  if required.isEmpty then
    throwError "No compiled inline specifications were found"
  -- Reuse the model mapping already produced from Rust annotations/extraction.
  -- Deriving both Specs and Required from a smaller subset cannot hide a root.
  -- The manifest is an audited data input produced from source ownership and
  -- extraction. Validate its schema and mode before using any names/counts;
  -- a development manifest still must satisfy the same compiled binding checks.
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
  let mut expectedLocalRust : Array String := #[]
  let mut expectedModels : Array Name := #[]
  for (rustName, entry) in entries.toArray do
    let .ok kind := entry.getObjValAs? String "kind"
      | throwError "Binding for {rustName} must name its owner kind"
    let .ok raw := entry.getObjValAs? String "raw"
      | throwError "Binding for {rustName} must name its exact extracted carrier"
    let .ok generics := entry.getObjValAs? (Array String) "generics"
      | throwError "Binding for {rustName} must name its original type parameters"
    let rawName := raw.toName
    -- Function entries bind a source spec to the exact extracted constant and
    -- its complete type/value prefix. Type entries bind nominal raw ownership
    -- to shape and full-provider declarations in their generated modules.
    if kind == "function" then
      if expectedModels.contains rawName then
        throwError "Model bindings repeat model {rawName}"
      expectedModels := expectedModels.push rawName
      let .ok sourceSpec := entry.getObjValAs? String "spec"
        | throwError "Function binding for {rustName} must name its inline specification"
      let .ok sourceInputs := entry.getObjValAs? (Array String) "inputs"
        | throwError "Function binding for {rustName} must name its original value inputs"
      let specName := (`Zerocopy.Specs).str sourceSpec
      unless env.getModuleIdxFor? specName == some specsModule do
        throwError "Function binding for {rustName} does not name a compiled inline specification"
      let (boundModel, boundInputs) ← AeneasSpecs.specBinding specName
      -- This also rejects a same-arity call on replaced or reordered inputs:
      -- specBinding already checked each argument's original variable identity.
      unless boundModel == rawName && boundInputs == generics.size + sourceInputs.size do
        throwError "Compiled specification {specName} changed its source model or original input prefix"
    else if kind == "type" then
      if expectedTypes.contains rawName then
        throwError "Type bindings repeat extracted carrier {rawName}"
      expectedTypes := expectedTypes.push rawName
      expectedLocalRust := expectedLocalRust.push rustName
      let some (.inductInfo rawInfo) := env.find? rawName
        | throwError "Type binding is not a raw nominal carrier: {rawName}"
      unless env.getModuleIdxFor? rawName == some typesModule &&
          rawInfo.numParams == generics.size do
        throwError "Raw nominal binding changed its ownership or type parameters: {rawName}"
      let (fields, mathType, decoder, provider, count) ← AeneasSpecs.modelBinding rawName
      unless count == generics.size do
        throwError "Mathematical model changed its original generic parameters: {rawName}"
      -- Compare independently emitted manifest names with the registry's actual
      -- declarations. Derived fixed names still need this external comparison;
      -- a correct provider for the wrong Rust owner is not an acceptable proof.
      for (key, actual) in #[("fields", fields), ("model", mathType),
          ("decoder", decoder), ("provider", provider)] do
        let .ok expected := entry.getObjValAs? String key
          | throwError "Type binding for {rustName} must name its {key}"
        unless actual == expected.toName do
          throwError "Compiled {key} {actual} disagrees with its Rust owner binding {expected}"
      -- Shapes can depend on mathematical child types before any decoder is
      -- built. Their ownership stays separate from full decoder/provider assembly.
      unless env.getModuleIdxFor? fields == some shapesModule &&
          env.getModuleIdxFor? mathType == some shapesModule do
        throwError "Mathematical fields and model must be owned by ModelShapes: {rawName}"
      unless env.getModuleIdxFor? decoder == some modelsModule &&
          env.getModuleIdxFor? provider == some modelsModule do
        throwError "Decoder and provider must be owned by Models: {rawName}"
      let .ok authored := entry.getObjValAs? Bool "authored"
        | throwError "Type binding must record its authored model disposition"
      -- An unannotated owner must receive its structural carrier, not an
      -- arbitrary smaller interpretation introduced by generation.
      unless authored || mathType == fields do
        throwError "Unannotated model must use its nominal Fields carrier: {rawName}"
    else
      throwError "Unsupported binding kind {kind} for {rustName}"
  -- This image is classified from LLBC type and trait declarations in live
  -- mode. Every compiled raw inductive must belong to exactly one class;
  -- local nominals must also have the source-bound model/provider entry above.
  let .ok image := bindings.getObjValAs? (Array Json) "type_image"
    | throwError "Model bindings must contain the complete raw type image"
  let mut imageTypes : Array Name := #[]
  let mut imageLocalTypes : Array Name := #[]
  let mut imageLocalRust : Array String := #[]
  let mut imageRust : Array String := #[]
  for row in image do
    let .ok rust := row.getObjValAs? String "rust"
      | throwError "Raw type image entry must name its Rust identity"
    let .ok raw := row.getObjValAs? String "raw"
      | throwError "Raw type image entry must name its generated carrier"
    let .ok category := row.getObjValAs? String "category"
      | throwError "Raw type image entry must name its extraction category"
    let .ok parameterCount := row.getObjValAs? Nat "parameters"
      | throwError "Raw type image entry must name its generated parameter count"
    unless category == "local-nominal" || category == "trait-dictionary" ||
        category == "external-nominal" do
      throwError "Unsupported raw type image category {category} for {rust}"
    let rawName := raw.toName
    if imageRust.contains rust || imageTypes.contains rawName then
      throwError "Raw type image repeats Rust identity or generated carrier {rust}: {rawName}"
    imageRust := imageRust.push rust
    imageTypes := imageTypes.push rawName
    let some (.inductInfo info) := env.find? rawName
      | throwError "Raw type image entry is not an inductive carrier: {rawName}"
    unless env.getModuleIdxFor? rawName == some typesModule && info.numParams == parameterCount do
      throwError "Raw type image changed its compiled module or parameter count: {rawName}"
    if category == "local-nominal" then
      let some bound := entries.get? rust
        | throwError "Local raw type image has no source binding: {rust}"
      let .ok boundRaw := bound.getObjValAs? String "raw"
        | throwError "Local raw type image has no bound generated carrier: {rust}"
      unless boundRaw == raw do
        throwError "Local raw type image disagrees with source-bound carrier: {rust}"
      imageLocalTypes := imageLocalTypes.push rawName
      imageLocalRust := imageLocalRust.push rust
  let missingLocalTypes := expectedTypes.filter (!imageLocalTypes.contains ·)
  let extraLocalTypes := imageLocalTypes.filter (!expectedTypes.contains ·)
  let missingLocalRust := expectedLocalRust.filter (!imageLocalRust.contains ·)
  let extraLocalRust := imageLocalRust.filter (!expectedLocalRust.contains ·)
  unless missingLocalTypes.isEmpty && extraLocalTypes.isEmpty &&
      missingLocalRust.isEmpty && extraLocalRust.isEmpty do
    throwError "Source-bound nominal models disagree with raw type image: missing {missingLocalTypes}; unexpected {extraLocalTypes}"
  let mut actualTypes : Array Name := #[]
  for (constName, constInfo) in env.constants.toList do
    if env.getModuleIdxFor? constName == some typesModule then
      if let .inductInfo _ := constInfo then
        actualTypes := actualTypes.push constName
  let missingTypes := actualTypes.filter (!imageTypes.contains ·)
  let extraTypes := imageTypes.filter (!actualTypes.contains ·)
  unless missingTypes.isEmpty && extraTypes.isEmpty do
    throwError "Compiled raw types disagree with classified extraction image: missing {missingTypes}; unexpected {extraTypes}"
  -- Compare registered providers too: a raw type can be present in extraction
  -- and the manifest while its full mathematical provider is absent or extra.
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
  -- Sort only for reproducible diagnostics and dependency output. Coverage was
  -- established from complete sets above, independent of declaration order.
  required := required.qsort (fun a b => a.toString < b.toString)
  let some checksModule := env.getModuleIdx? `Required
    | throwError "Required checks must be imported from their own module"
  for declName in required do
    let some (.thmInfo info) := env.find? declName
      | throwError "Missing required theorem {declName}"
    let specName := (`Zerocopy.Specs).str declName.getString!
    unless env.contains specName do
      throwError "Missing inline specification {specName}"
    -- Require the canonical theorem's type to name its exact spec. An arbitrary
    -- term or independently reproved proposition could bypass the inline claim.
    let actualSpec ← AeneasContracts.canonicalSpecName declName
    unless actualSpec == specName do
      throwError "{declName} must directly name its inline specification {specName}"
    unless ← Meta.isDefEq info.type (mkConst specName) do
      throwError "{declName} does not prove its inline specification {specName}"
    AeneasSpecs.checkSpecContract specName
    unless (env.getModuleIdxFor? declName).any proofModules.contains do
      throwError "{declName} must be declared in a configured proof module"
    let obligationName := (`Zerocopy.Obligations).str declName.getString!
    let adequacyName := obligationName.appendAfter "_adequate"
    let some (.thmInfo adequacy) := env.find? adequacyName
      | throwError "Missing arbitrary-outcome required theorem {adequacyName}"
    -- Reconstruct the arbitrary-outcome implication from compiled families.
    -- A concrete checked theorem alone would not expose weak posts, accidental
    -- divergence allowance, or a decoder/ghost that narrowed the required domain.
    let adequacyType ← AeneasContracts.contractAdequacyType specName obligationName
    unless ← Meta.isDefEq adequacy.type adequacyType do
      throwError "{adequacyName} does not prove its arbitrary-outcome required implication"
    unless env.getModuleIdxFor? adequacyName == some checksModule do
      throwError "{adequacyName} must be declared in the required checks module"
    -- The concrete witness is the separately named required proposition, and
    -- must be owned by the check module along with the adequacy theorem.
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
  -- Audit generated specs/models and handwritten helpers, not only canonical
  -- roots. A helper with an unapproved axiom must fail even if a current proof
  -- happens not to use it. privateToUserName keeps private namespace helpers in
  -- scope; module ownership catches auxiliaries with compiler-generated names.
  let prefixes := #[`Zerocopy, `core.num, `AeneasContracts, `AeneasSpecs,
    `ContractTests, `SpecsSyntaxTests, `SupportTests, `ContractAuditTests]
  let mut audited := 0
  for (declName, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName declName)) ||
        (env.getModuleIdxFor? declName).any auditModules.contains ||
        env.getModuleIdxFor? declName == some checksModule then
      let used ← collectAxioms declName
      for ax in used do
        -- These are Lean's permitted logical axioms. The only additional
        -- allowances are the ABI data inputs and opaque carrier whose exact
        -- signatures were checked above. Neither supplies a proposition;
        -- sorryAx and user-defined proof axioms remain errors.
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax ||
            modelInputs.contains ax || opaqueCarriers.contains ax do
          throwError "{declName} depends on unapproved axiom {ax}"
      audited := audited + 1
  IO.FS.writeFile "proof-dependencies.json" (Json.arr graph).pretty
  logInfo m!"Checked axiom dependencies of {audited} declarations"
