/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Validity
public meta import Lean
public section

open Lean Elab Term Meta
namespace AeneasSpecs

private meta initialize invariantExtension :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (carrier, predicate) => s.insert carrier predicate
    addImportedFn := fun entries => entries.foldl (fun s es =>
      es.foldl (fun s (carrier, predicate) => s.insert carrier predicate) s) {}
  }

/-- Every original type parameter has a dictionary, including unused ones. -/
meta def withValidityDictionaries (params : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α := do
  let rec loop (i : Nat) (dicts : Array Expr) : TermElabM α := do
    if h : i < params.size then
      let param := params[i]
      unless (← whnf (← inferType param)).isSort do
        throwError "Only Rust type parameters are supported in validity generation"
      let classType ← mkAppM ``IsValid #[param]
      let dictionaryName ← mkFreshUserName (Name.mkSimple s!"valid_{i}")
      withLocalDecl dictionaryName .instImplicit classType fun dict =>
        loop (i + 1) (dicts.push dict)
    else k dicts
  loop 0 #[]

private meta def addDefinition (declName : Name) (levels : List Name)
    (carrierType value : Expr) : TermElabM Unit := do
  addAndCompile (.defnDecl {
    «name» := declName, levelParams := levels, type := carrierType, value, hints := .abbrev, safety := .safe
  })

private meta def nominal (declName : Name) (count : Nat) : TermElabM InductiveVal := do
  let info ← getConstInfoInduct declName
  unless info.numParams == count && info.numIndices == 0 &&
      !info.isRec && info.all == [declName] do
    throwError "Validity requires a nonrecursive, nonindexed nominal Rust type: {declName}"
  pure info

meta def ensureStructuralValidityPhase : MetaM Unit := do
  if (← getEnv).contains `AeneasSpecs.unrestricted then
    throwError "Structural validity and invariants must elaborate before importing ValidityFallback"

/-- This command is emitted only for an exactly bound Rust type annotation.
Its predicate elaborates before the carrier's instance exists and before the
unrestricted fallback is imported. Self-reference and missing children fail. -/
syntax (name := authoredInvariant) "aeneas_invariant " ident " for " ident " with " num
    " type " "parameters" " := " term : command

elab_rules : command
  | `(aeneas_invariant $id:ident for $model:ident with $count:num type parameters := $predicate:term) =>
    Command.liftTermElabM do
      ensureStructuralValidityPhase
      let carrier ← realizeGlobalConstNoOverloadWithInfo model
      let info ← nominal carrier count.getNat
      if (invariantExtension.getState (← getEnv)).contains carrier then
        throwErrorAt model "Duplicate invariant for {carrier}"
      let declName := (← getCurrNamespace) ++ id.getId
      forallTelescope info.type fun params _ =>
        withValidityDictionaries params fun dicts => do
          let ty := mkAppN (Lean.mkConst carrier (info.levelParams.map Level.param)) params
          let expected ← mkArrow ty (mkSort .zero)
          let body ← elabTermEnsuringType predicate expected
          synthesizeSyntheticMVarsNoPostponing
          let value ← mkLambdaFVars (params ++ dicts) (← instantiateMVars body)
          addDefinition declName info.levelParams (← inferType value) value
      modifyEnv (invariantExtension.addEntry · (carrier, declName))

/-- Derive representation validity in the model's declaration order. Fields
are checked recursively; an authored predicate is an additional conjunct.
No fallback is available here, and aliases receive no competing instance. -/
elab "derive_model_validity " model:ident " with " count:num
    " type " "parameters" : command => Command.liftTermElabM do
  ensureStructuralValidityPhase
  let carrier ← realizeGlobalConstNoOverloadWithInfo model
  let info ← nominal carrier count.getNat
  let declName := carrier ++ `aeneasValid
  if (← getEnv).contains declName then
    throwErrorAt model "Duplicate structural validity for {carrier}"
  let levels := info.levelParams.map Level.param
  let value ← forallTelescope info.type fun params _ =>
    withValidityDictionaries params fun dicts => do
      let ty := mkAppN (Lean.mkConst carrier levels) params
      withLocalDeclD `self ty fun self => do
        let mut branches := #[]
        for ctor in info.ctors do
          let ctorTy ← inferType (mkAppN (Lean.mkConst ctor levels) params)
          let branch ← forallTelescope ctorTy fun fields _ => do
            let mut prop := Lean.mkConst ``True
            for field in fields.reverse do
              let fieldTy ← inferType field
              rejectEscapingFunctions fieldTy
              let valid ← mkAppM ``isValid #[field]
              prop ← mkAppM ``And #[valid, prop]
            mkLambdaFVars fields prop
          branches := branches.push branch
        let motive ← mkLambdaFVars #[self] (mkSort .zero)
        let structural ← if let some structureInfo := getStructureInfo? (← getEnv) carrier then do
            let mut prop := Lean.mkConst ``True
            for index in [:structureInfo.fieldNames.size] do
              let field := mkProj carrier index self
              let valid ← mkAppM ``isValid #[field]
              prop ← mkAppM ``And #[valid, prop]
            pure prop
          else if (← info.ctors.allM fun ctor => do
              let ctorInfo ← getConstInfoCtor ctor
              pure (ctorInfo.numFields == 0)) then
            pure (Lean.mkConst ``True)
          else pure (mkAppN (Lean.mkConst (mkCasesOnName carrier)
            (.succ .zero :: levels)) (params ++ #[motive, self] ++ branches))
        let prop ← match (invariantExtension.getState (← getEnv)).find? carrier with
          | none => pure structural
          | some predicate => do
            let authored := mkAppN (Lean.mkConst predicate levels) (params ++ dicts ++ #[self])
            mkAppM ``And #[structural, authored]
        let predicate ← mkLambdaFVars #[self] prop
        let instanceValue ← mkAppM ``IsValid.mk #[predicate]
        mkLambdaFVars (params ++ dicts) instanceValue
  addDefinition declName info.levelParams (← inferType value) value
  setReducibilityStatus declName .reducible
  addInstance declName .global 1000
  registerCanonicalValidity declName

private meta def canonicalInstance? (carrierType : Expr) : MetaM (Option Expr) := do
  let goal ← mkAppM ``IsValid #[carrierType]
  let mut found := none
  for provider in (← canonicalValidityProviders) do
    let candidate ← withoutModifyingState do
      let constant ← mkConstWithFreshMVarLevels provider
      let (args, _, target) ← forallMetaTelescopeReducing (← inferType constant)
      unless (← isDefEq target goal) do return none
      for arg in args do
        if arg.isMVar && !(← arg.mvarId!.isAssigned) then
          let argType ← instantiateMVars (← inferType arg)
          unless (← isClass? argType).isSome do
            throwError "Canonical validity has an unresolved parameter: {provider}"
          arg.mvarId!.assign (← synthInstance argType)
      let candidate ← instantiateMVars (mkAppN constant args)
      if candidate.hasMVar then throwError "Unresolved canonical validity: {provider}"
      return some candidate
    if let some candidate := candidate then
      if found.isSome then
        throwError "Ambiguous canonical validity for {carrierType}"
      found := some candidate
  return found

private meta partial def checkCanonical (carrierType : Expr) (inputs : Array Expr)
    (declName : Name) (levels : List Name) : TermElabM Unit := do
  rejectEscapingFunctions carrierType
  let carrierType ← whnf carrierType
  for arg in carrierType.getAppArgs do
    if (← whnf (← inferType arg)).isSort then
      checkCanonical arg inputs declName levels
  let some expected ← canonicalInstance? carrierType | return
  let actual ← synthInstance (← mkAppM ``IsValid #[carrierType])
  -- Equality and reflexivity are kernel checked, including container and native
  -- providers. Local generic dictionaries remain arbitrary conditional predicates.
  unless (← withTransparency .all (isDefEq actual expected)) do
    throwError "Conflicting canonical validity instance for {carrierType}"
  let equality ← mkEq actual expected
  let witness ← mkLambdaFVars inputs (← mkEqRefl expected)
  let witnessType ← mkForallFVars inputs equality
  let witnessName ← mkFreshUserName declName
  let declaration : TheoremVal := ⟨⟨witnessName, levels, witnessType⟩,
    witness, [witnessName]⟩
  addDecl (.thmDecl declaration)

/-- Registered authored predicates, for the final manifest audit in both directions. -/
meta def authoredInvariantNames : MetaM (Array Name) := do
  return ((invariantExtension.getState (← getEnv)).toList.map (·.2)).toArray

/-- The expected binding is read from generated metadata and checked against the
actual derived dictionary expression, rather than trusting registration alone. -/
meta def invariantBinding (predicateName : Name) : MetaM (Name × Name × Nat) := do
  let bindings := (invariantExtension.getState (← getEnv)).toList.filter
    (fun (_, predicate) => predicate == predicateName)
  let [(carrier, _)] := bindings
    | throwError "Missing or ambiguous invariant binding for {predicateName}"
  let info ← getConstInfoInduct carrier
  let instanceName := carrier ++ `aeneasValid
  unless (← getEnv).contains instanceName && (← Meta.isInstance instanceName) do
    throwError "Missing registered derived validity instance for {carrier}"
  let .defnInfo instanceDefinition ← getConstInfo instanceName
    | throwError "Missing derived validity instance for {carrier}"
  let .defnInfo _ ← getConstInfo predicateName
    | throwError "Invariant is not a generated predicate: {predicateName}"
  lambdaTelescope instanceDefinition.value fun originals body => do
    unless originals.size == 2 * info.numParams && body.getAppFn.isConstOf ``IsValid.mk do
      throwError "Unsupported derived validity instance for {carrier}"
    let args := body.getAppArgs
    unless args.size == 2 do throwError "Invalid derived dictionary for {carrier}"
    lambdaTelescope args[1]! fun values proposition => do
      unless values.size == 1 && proposition.isAppOfArity ``And 2 do
        throwError "Authored invariant is absent from derived validity for {carrier}"
      let authored := proposition.getAppArgs[1]!
      unless authored.getAppFn.isConstOf predicateName &&
          authored.getAppArgs == originals ++ values do
        throwError "Derived validity does not apply its invariant to the original parameters for {carrier}"
  return (carrier, instanceName, info.numParams)

elab "check_invariant_binding " predicate:ident " for " model:ident " with " count:num
    " type " "parameters" : command => Command.liftTermElabM do
  let predicateName ← realizeGlobalConstNoOverloadWithInfo predicate
  let modelName ← realizeGlobalConstNoOverloadWithInfo model
  let (carrier, _, parameterCount) ← invariantBinding predicateName
  unless carrier == modelName && parameterCount == count.getNat do
    throwError "Invariant is not attached to the verified Rust type: {predicateName}"

syntax "aeneas_invariant_begin " command " aeneas_invariant_end" : command
macro_rules
  | `(aeneas_invariant_begin $declaration:command aeneas_invariant_end) => do
    unless declaration.raw.getKind == ``authoredInvariant do
      Macro.throwErrorAt declaration "An Aeneas type fence must contain exactly one invariant declaration"
    pure declaration.raw

/-- Check actual generic and concrete carriers used by a function in exactly
the original model context plus its generated dictionaries, before ghosts. -/
elab "check_model_validity_inputs " model:ident " with " count:num
    " type " "parameters" : command => Command.liftTermElabM do
  let modelName ← realizeGlobalConstNoOverloadWithInfo model
  let info ← getConstInfo modelName
  forallTelescope info.type fun inputs result => do
    unless inputs.size ≥ count.getNat do
      throwErrorAt model "Invalid Rust type parameter count"
    let generics := inputs.extract 0 count.getNat
    withValidityDictionaries generics fun dicts => do
      let boundInputs := inputs ++ dicts
      for input in inputs.extract count.getNat inputs.size do
        if (← whnf (← inferType input)).isSort then
          throwErrorAt model "Rust type parameter count omits an original type parameter"
        checkCanonical (← inferType input) boundInputs
          (modelName.appendAfter "_input_validity") info.levelParams
      let result ← whnf result
      unless result.isAppOfArity ``Aeneas.Std.Result 1 do
        throwErrorAt model "Unsupported result or escaping borrow in {modelName}"
      checkCanonical result.appArg! boundInputs
        (modelName.appendAfter "_output_validity") info.levelParams

end AeneasSpecs
