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

open Lean Elab Term Meta Aeneas.Std
namespace AeneasSpecs

structure ModelBinding where
  raw : Name
  fields : Name
  model : Name
  decoder : Name
  provider : Name
  generics : Nat
  deriving Inhabited

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
  throwError "Unsupported opaque carrier or missing bound model provider: {raw}"

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
  if (modelExtension.getState (← getEnv)).contains raw then
    throwError "Duplicate mathematical model shape for {raw}"
  modifyEnv (modelExtension.addEntry · {
    raw, fields := raw ++ `Fields, «model» := mathName, decoder := raw ++ `decode,
    provider := raw ++ `aeneasModel, generics := count })

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
      let body ← if let some structureInfo := getStructureInfo? (← getEnv) raw then
          decodeBranch (structureInfo.fieldNames.mapIdx fun i _ => mkProj raw i rawValue)
            ((← getConstInfoInduct b.fields).ctors.head!)
        else do
          let mut branches := #[]
          for ctor in info.ctors do
            let branch ← forallTelescope (← inferType (mkAppN (mkConst ctor levels) params)) fun fields _ => do
              let body ← decodeBranch fields (b.fields ++ Name.mkSimple ctor.getString!)
              mkLambdaFVars fields body
            branches := branches.push branch
          let motive ← mkLambdaFVars #[rawValue] outputTy
          pure (mkAppN (mkConst (mkCasesOnName raw) ((← getLevel outputTy) :: levels))
            (params ++ #[motive, rawValue] ++ branches))
      mkLambdaFVars #[rawValue] body
    addDefinition b.decoder info.levelParams (← mkLambdaFVars all full)
    -- Keep child witnesses even when decodeFields intentionally forgets them.
    -- This proposition follows the actual fixed providers and constructor path.
    let decomposition ← withLocalDeclD `raw rawTy fun rawValue =>
      withLocalDeclD `model modelTy fun modelValue => do
        let someModel ← mkAppM ``Option.some #[modelValue]
        let branch (fields : Array Expr) (constructor : Name) : TermElabM Expr := do
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
        let rhs ← if let some structureInfo := getStructureInfo? (← getEnv) raw then
            branch (structureInfo.fieldNames.mapIdx fun i _ => mkProj raw i rawValue)
              ((← getConstInfoInduct b.fields).ctors.head!)
          else do
            let mut branches := #[]
            for ctor in info.ctors do
              let value ← forallTelescope (← inferType (mkAppN (mkConst ctor levels) params)) fun fields _ => do
                mkLambdaFVars fields (← branch fields (b.fields ++ Name.mkSimple ctor.getString!))
              branches := branches.push value
            let motive ← mkLambdaFVars #[rawValue] (mkSort .zero)
            pure (mkAppN (mkConst (mkCasesOnName raw) (.succ .zero :: levels))
              (params ++ #[motive, rawValue] ++ branches))
        let lhs ← mkEq (mkApp (mkAppN (mkConst b.decoder levels) all) rawValue) someModel
        let proposition ← mkAppM ``Iff #[lhs, rhs]
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
