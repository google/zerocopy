/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
public import ModelCompletion
public meta import Lean
public section

/-!
Rust values have an extracted representation and a mathematical interpretation.
This module builds the connection in two stages. A shape declares the decoded
field types using only mathematical child types. A provider later supplies the
actual child decoders and combines their accepted values with the local decoder.
Separating those stages lets ordinary support lemmas mention shapes before full
providers exist.

The full decoder must visit every field even when the local model discards its
information. For an enum it visits only the selected constructor's payload. The
same constructor traversal produces a kernel-checked decomposition theorem,
which exposes those child witnesses to operation proofs. The registry preserves
nominal ownership across module imports; it supplies explicit providers rather
than allowing later authored instances to select a different interpretation.
-/

open Lean Elab Term Meta Aeneas.Std
namespace AeneasSpecs

/-- The registration records the Rust owner, its authored mathematical type,
and the original generic count. The generated declarations have fixed names
under that owner, so they are derived rather than stored as independent state. -/
structure ModelBinding where
  raw : Name
  model : Name
  generics : Nat
  deriving Inhabited

meta def ModelBinding.fields (binding : ModelBinding) : Name := binding.raw ++ `Fields
meta def ModelBinding.decoder (binding : ModelBinding) : Name := binding.raw ++ `decode
meta def ModelBinding.provider (binding : ModelBinding) : Name := binding.raw ++ `aeneasModel

-- A persistent extension carries model registrations into importing modules.
-- Lean merges imported entries before this module's entries, so nominal child
-- shapes and providers can be resolved without relying on declaration text.
private meta initialize modelExtension :
    SimplePersistentEnvExtension ModelBinding (NameMap ModelBinding) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s b => s.insert b.raw b
    addImportedFn := fun entries => entries.foldl (fun s es =>
      es.foldl (fun s b => s.insert b.raw b) s) {}
  }

meta def modelOwnerNames : MetaM (Array Name) := do
  return ((modelExtension.getState (← getEnv)).toList.map (·.1)).toArray

meta def modelBinding (raw : Name) : MetaM (Name × Name × Name × Name × Nat) := do
  let some b := (modelExtension.getState (← getEnv)).find? raw
    | throwError "Missing mathematical model binding for {raw}"
  unless (← getEnv).contains b.provider && (← getEnv).contains b.decoder do
    throwError "Missing full decoder or bound provider for {raw}"
  return (b.fields, b.model, b.decoder, b.provider, b.generics)

/-- One dictionary for every original Rust generic, including unused parameters. -/
meta def withModelDictionaries (params : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let rec loop (i : Nat) (dicts : Array Expr) : TermElabM α := do
    if h : i < params.size then
      let param := params[i]
      unless (← whnf (← inferType param)).isSort do
        throwError "Only Rust type parameters are supported in model generation"
      let classType ← mkAppM ``RustModel #[param]
      withLocalDecl (Name.mkSimple s!"_rustModel{i}") .instImplicit classType fun dict =>
        loop (i + 1) (dicts.push dict)
    else k dicts
  loop 0 #[]

/-- These restrictions describe the supported extracted shape. Indexed types
and recursive groups would require additional carrier and decoding semantics;
accepting them through the simple constructor traversal would invent a model. -/
private meta def nominal (raw : Name) (count : Nat) : TermElabM InductiveVal := do
  let info ← getConstInfoInduct raw
  unless info.numParams == count && info.numIndices == 0 &&
      !info.isRec && info.all == [raw] do
    throwError "Models require a nonrecursive, nonindexed nominal Rust type: {raw}"
  pure info

/-- Fixed structural selection. No global instance inference selects automatic
model meanings, even when authored ghosts later introduce competing instances. -/
meta partial def boundModelProvider (raw : Expr) (params dicts : Array Expr) : MetaM Expr := do
  rejectEscapingFunctions raw
  let raw ← whnf raw
  -- A generic's original dictionary fixes its meaning even when no field uses
  -- it. Resolve it before structural cases or any authored local instances.
  for i in [:params.size] do
    if raw == params[i]! then return dicts[i]!
  let args := raw.getAppArgs
  let head := raw.getAppFn
  let app (n : Name) (xs : Array Expr) : MetaM Expr := do
    mkAppOptM n (xs.map some)
  if head.isConstOf ``UScalar then return ← app ``modelUScalar args
  if head.isConstOf ``IScalar then return ← app ``modelIScalar args
  if head.isConstOf ``Bool then return mkConst ``modelBool
  if head.isConstOf ``Nat then return mkConst ``modelNat
  if head.isConstOf ``Int then return mkConst ``modelInt
  if head.isConstOf ``Unit then return mkConst ``modelUnit
  if head.isConstOf ``Prod || head.isConstOf ``core.result.Result then
    let ma ← boundModelProvider args[0]! params dicts
    let mb ← boundModelProvider args[1]! params dicts
    return ← app (if head.isConstOf ``Prod then ``modelProd else ``modelRustResult)
      (args ++ #[ma, mb])
  if head.isConstOf ``Option || head.isConstOf ``List || head.isConstOf ``Slice then
    let ma ← boundModelProvider args[0]! params dicts
    let provider := if head.isConstOf ``Option then ``modelOption
      else if head.isConstOf ``List then ``modelList else ``modelSlice
    return ← app provider (args ++ #[ma])
  if head.isConstOf ``Aeneas.Std.Array then
    let ma ← boundModelProvider args[0]! params dicts
    return ← app ``modelArray (args ++ #[ma])
  if head.isConstOf ``core.num.nonzero.NonZero then
    let word ← whnf args[0]!
    if word.getAppFn.isConstOf ``UScalar then
      return ← app ``modelNonZeroUScalar #[word.appArg!, args[1]!]
    if word.getAppFn.isConstOf ``IScalar then
      return ← app ``modelNonZeroIScalar #[word.appArg!, args[1]!]
  if let .const n _ := head then
    if let some b := (modelExtension.getState (← getEnv)).find? n then
      unless (← getEnv).contains b.provider do
        throwError "Full model provider is not available for {n}"
      let childDicts ← args.mapM fun a => boundModelProvider a params dicts
      return ← app b.provider (args ++ childDicts)
  -- A universal fallback would admit values without a defined interpretation.
  -- Unsupported carriers must fail at model construction, not weaken a proof.
  throwError "Unsupported opaque carrier or missing bound model provider: {raw}"

/-- Reduce associated mathematical types recursively, while leaving values
alone. Nested containers then elaborate against ordinary mathematical carriers,
without asking instance inference to reverse-map a model type to a raw type. -/
private meta partial def reduceModelTypes (e : Expr) : MetaM Expr := do
  let e ← withTransparency .all (whnf e)
  if e.isApp then
    let mut args := #[]
    for arg in e.getAppArgs do
      let reducedArg ← if (← isType arg) then reduceModelTypes arg else pure arg
      args := args.push reducedArg
    return mkAppN e.getAppFn args
  return e

meta def providerModel (raw provider : Expr) : MetaM Expr := do
  reduceModelTypes (← mkAppOptM ``RustModel.Model #[some raw, some provider])

meta def providerDecode (raw provider value : Expr) : MetaM Expr :=
  mkAppOptM ``RustModel.decode #[some raw, some provider, some value]

/-- Shape families depend only on mathematical carrier types. No decoder
provider is required for a nominal child whose shape has already been declared. -/
private meta partial def shapeType (raw : Expr) (params models : Array Expr) : MetaM Expr := do
  rejectEscapingFunctions raw
  let raw ← whnf raw
  for i in [:params.size] do
    if raw == params[i]! then return models[i]!
  let args := raw.getAppArgs
  let head := raw.getAppFn
  if let .const n _ := head then
    if let some b := (modelExtension.getState (← getEnv)).find? n then
      let children ← args.mapM fun a => shapeType a params models
      return ← mkAppOptM b.model (children.map some)
  if head.isConstOf ``Prod || head.isConstOf ``core.result.Result then
    let children ← args.mapM fun a => shapeType a params models
    return mkAppN (← mkConstWithFreshMVarLevels head.constName!) children
  if head.isConstOf ``Option || head.isConstOf ``List then
    return mkAppN (← mkConstWithFreshMVarLevels head.constName!)
      #[← shapeType args[0]! params models]
  if head.isConstOf ``Slice then
    return ← mkAppM ``SliceValue #[← shapeType args[0]! params models]
  if head.isConstOf ``Aeneas.Std.Array then
    return ← mkAppM ``ArrayValue #[← shapeType args[0]! params models, args[1]!]
  -- Scalar and nonzero carriers have fixed native mathematical types.
  providerModel raw (← boundModelProvider raw #[] #[])

/-- Shape generation binds one mathematical type per original generic. These
are types rather than RustModel dictionaries: declaring a child shape need not
wait for its decoder or any proofs used to construct that decoder. -/
private meta def withModelTypes (params : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let rec loop (i : Nat) (models : Array Expr) : TermElabM α := do
    if h : i < params.size then
      let p := params[i]
      let pName := (← p.fvarId!.getDecl).userName
      let modelName := Name.mkSimple s!"{pName}Model"
      withLocalDeclD modelName (← inferType p) fun model => loop (i + 1) (models.push model)
    else k models
  loop 0 #[]

private meta def expressionText (e : Expr) : TermElabM String := do
  return (← withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.universes false)
    (ppExpr e)).pretty 100000

private meta def parameterText (params dicts : Array Expr) : TermElabM String := do
  let mut text := ""
  for p in params do
    text := text ++ s!" ({(← p.fvarId!.getDecl).userName} : {← expressionText (← inferType p)})"
  for d in dicts do
    text := text ++ s!" [{(← d.fvarId!.getDecl).userName} : {← expressionText (← inferType d)}]"
  return text

private meta def parseCommand (text : String) : Command.CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .ok stx => pure stx
  | .error error => throwError "Generated mathematical declaration failed to parse: {error}\n{text}"

/-- Mirror the raw constructor structure with decoded field types. Parsing
ordinary Lean declarations lets Lean enforce the resulting type and constructor
rules rather than installing unchecked expression representations of a shape. -/
private meta def generateShape (raw : Name) (count : Nat) : Command.CommandElabM Unit := do
  let text ← Command.liftTermElabM do
    let info ← nominal raw count
    forallTelescope info.type fun params _ =>
      withModelTypes params fun models => do
        let binders ← parameterText models #[]
        let shapeName := "Fields"
        if let some structureInfo := getStructureInfo? (← getEnv) raw then
          let ctorTy := mkAppN (mkConst info.ctors.head! (info.levelParams.map Level.param)) params
          forallTelescope (← inferType ctorTy) fun fields _ => do
            let mut text := s!"structure {shapeName}{binders} where\n"
            for i in [:fields.size] do
              let ty ← shapeType (← inferType fields[i]!) params models
              text := text ++ s!"  {structureInfo.fieldNames[i]!.getString!} : {← expressionText ty}\n"
            return text
        else
          let mut text := s!"inductive {shapeName}{binders} where\n"
          for ctor in info.ctors do
            let ctorTy := mkAppN (mkConst ctor (info.levelParams.map Level.param)) params
            let fieldsText ← forallTelescope (← inferType ctorTy) fun fields _ => do
              let mut fieldsText := ""
              for field in fields do
                let ty ← shapeType (← inferType field) params models
                fieldsText := fieldsText ++ s!" → {← expressionText ty}"
              return fieldsText
            -- Print actual user names, never internal free-variable identifiers.
            let application ← models.foldlM (fun s e => do
              pure (s ++ " " ++ (← e.fvarId!.getDecl).userName.toString)) ""
            let fieldPrefix := if fieldsText.isEmpty then "" else fieldsText.drop 3 |>.toString
            let arrow := if fieldsText.isEmpty then "" else " → "
            text := text ++ s!"| {ctor.getString!} : {fieldPrefix}{arrow}@{shapeName}{application}\n"
          return text
  Command.withScope (fun scope => {scope with currNamespace := raw}) do
    Command.elabCommand (← parseCommand text)

syntax (name := modelStructure) "model " ident " where" Parser.Command.structFields : command
syntax (name := modelAlias) "model " ident " := " term : command
syntax "aeneas_model_shape " ident " with " num " type " "parameters" " begin "
  command " end" : command

private meta def registerShape (raw mathName : Name) (count : Nat) : Command.CommandElabM Unit := do
  -- One raw owner has one registered interpretation. A second shape must not
  -- silently replace the one already used by imported contracts or providers.
  if (modelExtension.getState (← getEnv)).contains raw then
    throwError "Duplicate mathematical model shape for {raw}"
  modifyEnv (modelExtension.addEntry · {
    raw, «model» := mathName, generics := count })

elab "derive_model_shape " rawId:ident " with " count:num " type " "parameters" : command => do
  let raw ← Command.liftTermElabM (realizeGlobalConstNoOverloadWithInfo rawId)
  generateShape raw count.getNat
  registerShape raw (raw ++ `Fields) count.getNat

elab_rules : command
  | `(aeneas_model_shape $rawId:ident with $count:num type parameters begin $declaration:command end) => do
    let raw ← Command.liftTermElabM (realizeGlobalConstNoOverloadWithInfo rawId)
    generateShape raw count.getNat
    let id : TSyntax `ident := ⟨declaration.raw[1]⟩
    let suffix ← if declaration.raw.getKind == ``modelStructure then do
        let fileMap ← getFileMap
        let column := declaration.raw[3].getPos?.map (fun p => (fileMap.toPosition p).column) |>.getD 2
        pure (" where\n" ++ String.ofList (List.replicate column ' ') ++ declaration.raw[3].reprint.getD "")
      else if declaration.raw.getKind == ``modelAlias then
        pure (" := " ++ declaration.raw[3].reprint.getD "")
      else throwError "A type fence must contain exactly one model shape declaration"
    -- Fields belongs to the generated structural carrier. An authored model
    -- may alias it, but cannot overwrite the name and change field admission.
    if id.getId == `Fields then throwError "Fields is the generated nominal field carrier"
    let (binders, application, levelNames) ← Command.liftTermElabM do
      let info ← nominal raw count.getNat
      forallTelescope info.type fun params _ => withModelTypes params fun models => do
        let binders ← parameterText models #[]
        let application ← models.foldlM (fun s e => do
          pure (s ++ " " ++ (← e.fvarId!.getDecl).userName.toString)) ""
        return (binders, application, info.levelParams)
    let suffix := if declaration.raw.getKind == ``modelAlias && declaration.raw[3].isIdent &&
        declaration.raw[3].getId == `Fields then " := @Fields" ++ application else suffix
    let authored := raw ++ id.getId
    let keyword := if declaration.raw.getKind == ``modelStructure then "@[ext] structure" else "abbrev"
    Command.withScope (fun scope =>
      {scope with
        currNamespace := raw
        levelNames := levelNames ++ scope.levelNames
        opts := scope.opts.setBool `autoImplicit false}) do
      Command.elabCommand (← parseCommand s!"{keyword} {id.getId}{binders}{suffix}")
    registerShape raw authored count.getNat

/-- Finish elaboration and install a kernel-checked definition. Its safe status
forbids unsafe dependencies; `forceExpose` lets importing modules reduce it.
Proof terms nested in the value also need exported names, even when the decoder
is noncomputable and used only to state mathematical contracts. -/
private meta def addDefinition (declName : Name) (levels : List Name) (value : Expr) : TermElabM Unit := do
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  -- Match native declaration assembly: nested proof auxiliaries must remain
  -- available when downstream modules unfold the exposed decoder.
  let value ← withExporting do
    withDeclNameForAuxNaming declName do
      abstractNestedProofs value
  addDecl (.defnDecl {
    «name» := declName, levelParams := levels, «type» := (← inferType value), value,
    hints := .abbrev, safety := .safe }) (forceExpose := true)
  -- Authored decoders may be logical noncomputable terms. The safe declaration
  -- is kernel checked and exposed for subsequent associated-type reduction;
  -- contracts do not require executable code for mathematical decoding.
  modifyEnv (addNoncomputable · declName)
  enableRealizationsForConst declName

/-- Assemble a case expression using the original nominal constructors.
A structure has one case whose fields are projections. An enum has one branch
per constructor, and that branch receives only the selected payload. Both the
full decoder and its decomposition theorem use this traversal so they cannot
silently disagree about field order or constructor correspondence. -/
private meta def nominalCases (raw fieldsName : Name) (info : InductiveVal)
    (params : Array Expr) (rawValue resultType : Expr)
    (branch : Array Expr → Name → TermElabM Expr) : TermElabM Expr := do
  let levels := info.levelParams.map Level.param
  if let some structureInfo := getStructureInfo? (← getEnv) raw then
    branch (structureInfo.fieldNames.mapIdx fun i _ => mkProj raw i rawValue)
      ((← getConstInfoInduct fieldsName).ctors.head!)
  else
    let mut branches := #[]
    for ctor in info.ctors do
      let ctorType ← inferType (mkAppN (mkConst ctor levels) params)
      let body ← forallTelescope ctorType fun fields _ => do
        mkLambdaFVars fields (← branch fields (fieldsName ++ Name.mkSimple ctor.getString!))
      branches := branches.push body
    -- casesOn needs a motive: the result type for each possible raw value.
    -- These decoders are not indexed, so the motive is constant in that value.
    let motive ← mkLambdaFVars #[rawValue] resultType
    pure (mkAppN (mkConst (mkCasesOnName raw) ((← getLevel resultType) :: levels))
      (params ++ #[motive, rawValue] ++ branches))

/-- Build the local decoder, wrap it with recursive field admission, prove
that wrapper's decomposition, and finally register the complete RustModel.
An absent local decoder is structural identity. An infallible authored decoder
returns a model; a fallible one returns Option model and can restrict admission. -/
private meta def deriveProvider (raw : Name) (count : Nat)
    (localDecoder : Option (Name × Syntax × Bool)) : TermElabM Unit := do
  let info ← nominal raw count
  let some b := (modelExtension.getState (← getEnv)).find? raw
    | throwError "Missing Fields/model shape for {raw}"
  if (← getEnv).contains b.provider then throwError "Duplicate model provider for {raw}"
  let levels := info.levelParams.map Level.param
  forallTelescope info.type fun params _ => withModelDictionaries params fun dicts => do
    let all := params ++ dicts
    let rawTy := mkAppN (mkConst raw levels) params
    let models ← params.zip dicts |>.mapM fun (p, d) => providerModel p d
    let fieldsTy ← mkAppOptM b.fields (models.map some)
    let modelTy ← mkAppOptM b.model (models.map some)
    let outputTy ← mkAppM ``Option #[modelTy]
    let localFn ← withLocalDeclD (localDecoder.map (·.1) |>.getD `self) fieldsTy fun fields => do
      let body ← match localDecoder with
        | none => mkAppM ``Option.some #[fields]
        | some (_, term, fallible) => do
          let completed ← withRef term `(model_value $(⟨term⟩))
          let value ← elabTermEnsuringType completed (if fallible then outputTy else modelTy)
          if fallible then pure value else mkAppM ``Option.some #[value]
      mkLambdaFVars #[fields] body
    addDefinition (raw ++ `decodeFields) info.levelParams (← mkLambdaFVars all localFn)
    let localConst := mkAppN (mkConst (raw ++ `decodeFields) levels) all
    let full ← withLocalDeclD `raw rawTy fun rawValue => do
      -- Bind each child decoder before constructing Fields. Option.bind stops
      -- on rejection; successful traversal supplies all decoded values in the
      -- original constructor order, including values the local decoder forgets.
      let decodeBranch (fields : Array Expr) (constructor : Name) : TermElabM Expr := do
        let rec loop (i : Nat) (decoded : Array Expr) : TermElabM Expr := do
          if h : i < fields.size then
            let field := fields[i]
            let fieldTy ← inferType field
            let provider ← boundModelProvider fieldTy params dicts
            let valueTy ← providerModel fieldTy provider
            let decodedRaw ← providerDecode fieldTy provider field
            withLocalDeclD (Name.mkSimple s!"field{i}") valueTy fun value => do
              let rest ← loop (i+1) (decoded.push value)
              let continuation ← mkLambdaFVars #[value] rest
              mkAppM ``Option.bind #[decodedRaw, continuation]
          else pure (mkApp localConst (mkAppN (mkConst constructor levels) (models ++ decoded)))
        loop 0 #[]
      let body ← nominalCases raw b.fields info params rawValue outputTy decodeBranch
      mkLambdaFVars #[rawValue] body
    addDefinition b.decoder info.levelParams (← mkLambdaFVars all full)
    -- Keep child witnesses even when decodeFields intentionally forgets them.
    -- This proposition follows the actual fixed providers and constructor path.
    let decomposition ← withLocalDeclD `raw rawTy fun rawValue =>
      withLocalDeclD `model modelTy fun modelValue => do
        let someModel ← mkAppM ``Option.some #[modelValue]
        let branch (fields : Array Expr) (constructor : Name) : TermElabM Expr := do
          -- This is the proposition corresponding to the Option.bind chain:
          -- each child has a witness and its decoder equation, followed by the
          -- local decoder equation. Keeping witnesses prevents lossy models
          -- from erasing the parent's recursive admission obligations.
          let rec decomposeLoop (i : Nat) (decoded : Array Expr) : TermElabM Expr := do
            if h : i < fields.size then
              let field := fields[i]
              let fieldTy ← inferType field
              let provider ← boundModelProvider fieldTy params dicts
              let valueTy ← providerModel fieldTy provider
              let decodedRaw ← providerDecode fieldTy provider field
              withLocalDeclD (Name.mkSimple s!"field{i}") valueTy fun value => do
                let equation ← mkEq decodedRaw (← mkAppM ``Option.some #[value])
                let rest ← decomposeLoop (i + 1) (decoded.push value)
                let body ← mkAppM ``And #[equation, rest]
                mkAppM ``Exists #[← mkLambdaFVars #[value] body]
            else
              let fields ← mkAppOptM constructor ((models ++ decoded).map some)
              mkEq (mkApp localConst fields) someModel
          decomposeLoop 0 #[]
        let rhs ← nominalCases raw b.fields info params rawValue (mkSort .zero) branch
        let lhs ← mkEq (mkApp (mkAppN (mkConst b.decoder levels) all) rawValue) someModel
        let proposition ← mkAppM ``Iff #[lhs, rhs]
        -- The bridge is proved by ordinary case splitting and bind expansion.
        -- It is not an axiom asserted merely because generation succeeded.
        let proofSyntax ← match Parser.runParserCategory (← getEnv) `term
            s!"by cases raw <;> simp only [{b.decoder}, Option.bind_eq_some_iff]" with
          | .ok stx => pure stx
          | .error error => throwError "Generated decoder decomposition failed to parse: {error}"
        let proof ← withOptions (fun o => o.setBool `linter.unusedSimpArgs false)
          (elabTermEnsuringType proofSyntax proposition)
        mkLambdaFVars (all ++ #[rawValue, modelValue]) proof
    synthesizeSyntheticMVarsNoPostponing
    let decomposition ← instantiateMVars decomposition
    addDecl (.thmDecl {
      «name» := raw ++ `decode_decompose, levelParams := info.levelParams,
      «type» := (← inferType decomposition), value := decomposition }) (forceExpose := true)
    let provider ← mkAppOptM ``RustModel.mk #[some rawTy, some modelTy,
      some (mkAppN (mkConst b.decoder levels) all)]
    addDefinition b.provider info.levelParams (← mkLambdaFVars all provider)
  setReducibilityStatus b.provider .reducible
  addInstance b.provider .global 1000

elab "derive_rust_model " rawId:ident " with " count:num " type " "parameters" : command =>
  Command.liftTermElabM do
    deriveProvider (← realizeGlobalConstNoOverloadWithInfo rawId) count.getNat none

elab "derive_rust_model " rawId:ident " with " count:num " type " "parameters"
    " decode " self:ident " => " body:term : command => Command.liftTermElabM do
  deriveProvider (← realizeGlobalConstNoOverloadWithInfo rawId) count.getNat
    (some (self.getId, body, false))

elab "derive_rust_model " rawId:ident " with " count:num " type " "parameters"
    " decode? " self:ident " => " body:term : command => Command.liftTermElabM do
  deriveProvider (← realizeGlobalConstNoOverloadWithInfo rawId) count.getNat
    (some (self.getId, body, true))

/-- Audit the elaborated provider against its registered raw owner, mathematical
type, full decoder, and generic count. Definitional equality unfolds actual
expressions, so matching names alone cannot attach a provider to a wrong type. -/
elab "check_model_binding " rawId:ident " with " count:num " type " "parameters" : command =>
  Command.liftTermElabM do
    let raw ← realizeGlobalConstNoOverloadWithInfo rawId
    let (fields, mathName, decoder, provider, generics) ← modelBinding raw
    unless generics == count.getNat do throwError "Wrong generic count for {raw}"
    let info ← nominal raw count.getNat
    forallTelescope info.type fun params _ => withModelDictionaries params fun dicts => do
      let all := params ++ dicts
      let rawTy := mkAppN (mkConst raw (info.levelParams.map Level.param)) params
      let providerExpr := mkAppN (mkConst provider (info.levelParams.map Level.param)) all
      unless (← isDefEq (← inferType providerExpr) (← mkAppM ``RustModel #[rawTy])) do
        throwError "Provider is attached to the wrong raw carrier: {raw}"
      unless (← withTransparency .all (isDefEq (← providerModel rawTy providerExpr)
          (← mkAppOptM mathName ((← params.zip dicts |>.mapM fun (p, d) => providerModel p d).map some)))) do
        throwError "Provider model is not the bound mathematical type: {raw}"
      withLocalDeclD `raw rawTy fun value => do
        unless (← withTransparency .all (isDefEq (← providerDecode rawTy providerExpr value)
            (mkAppN (mkConst decoder (info.levelParams.map Level.param)) (all.push value)))) do
          throwError "Provider decoder is not the bound full decoder: {raw}"
      unless (← getEnv).contains fields do throwError "Missing Fields carrier: {raw}"

/-- Check every original input and the successful output before a function's
specification is authored. Unsupported borrowed continuations or missing models
must fail even if a later clause would ignore the affected value. -/
elab "check_model_inputs " functionId:ident " with " count:num " type " "parameters" : command =>
  Command.liftTermElabM do
    let function ← realizeGlobalConstNoOverloadWithInfo functionId
    forallTelescope (← getConstInfo function).type fun inputs result => do
      unless count.getNat ≤ inputs.size do throwError "Invalid Rust generic prefix count"
      let params := inputs.extract 0 count.getNat
      withModelDictionaries params fun dicts => do
        for input in inputs.extract count.getNat inputs.size do
          let _ ← boundModelProvider (← inferType input) params dicts
        let result ← whnf result
        unless result.isAppOfArity ``Aeneas.Std.Result 1 do
          throwError "Unsupported result or escaping borrow in {function}"
        let _ ← boundModelProvider result.appArg! params dicts

end AeneasSpecs
