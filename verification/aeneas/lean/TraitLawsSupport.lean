/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DeriveModels
public meta import TraitDictionarySupport
public meta import Lean
public section

/-!
Rust trait dictionaries contain methods and associated values, but no proof that
those values obey the trait's documented contract. An inline trait invariant
adds a separate Lean proposition about the exact dictionary. Generic function
contracts receive that proposition as an assumption; concrete implementations
must provide a checked proof. The extracted function and its arguments stay
unchanged.

The registry identifies dictionary types from the checked extraction manifest.
It also identifies the law class for an annotated trait. An unannotated trait
has no additional law, rather than a default proof that every law is True.
-/

open Lean Elab Term Meta
namespace AeneasSpecs

/- Introduce laws for original dictionaries and their actual parent dictionary
fields. Parent projections preserve identity: a Child bound supplies the law
for that Child's Parent dictionary, not for an unrelated Parent implementation.
The generated assumptions are ordinary Lean instance binders, usable by step.
-/
/-- Apply a law with canonical providers, never authored instance inference. -/
meta def traitLawProposition (binding : TraitLawBinding) (carrier dictionary : Expr)
    (params models : Array Expr) : MetaM Expr := do
  let some law := binding.law | throwError "Dictionary has no annotated law"
  let arguments := carrier.getAppArgs
  let providers ← binding.modelParameters.mapM fun index => do
    unless index < arguments.size do throwError "Invalid trait model parameter index"
    boundModelProvider arguments[index]! params models
  mkAppOptM law ((arguments ++ #[dictionary] ++ providers).map some)

private meta partial def visitDictionaryLaws (pending : List (Expr × List Name))
    (params models laws : Array Expr) (k : Array Expr → TermElabM α) : TermElabM α := do
  match pending with
  | [] => k laws
  | (dictionary, ancestors) :: rest =>
    let carrier ← inferType dictionary
    let some binding ← traitDictionary? carrier
      | throwError "Unregistered extracted trait dictionary: {carrier}"
    if ancestors.contains binding.raw then
      throwError "Recursive parent trait dictionaries are unsupported: {binding.raw}"
    let mut parents := []
    if let some structureInfo := getStructureInfo? (← getEnv) binding.raw then
      for i in [:structureInfo.fieldNames.size] do
        let parent := mkProj binding.raw i dictionary
        if (← traitDictionary? (← inferType parent)).isSome then
          parents := parents ++ [(parent, binding.raw :: ancestors)]
    let next := parents ++ rest
    match binding.law with
    | none => visitDictionaryLaws next params models laws k
    | some law =>
      let proposition ← traitLawProposition binding carrier dictionary params models
      unless ← isProp proposition do
        throwError "Trait invariant is not a proposition: {law}"
      withLocalDecl (Name.mkSimple s!"_traitLaw{laws.size}") .instImplicit
          proposition fun evidence => visitDictionaryLaws next params models (laws.push evidence) k
meta def withTraitLawAssumptions (dictionaries params models : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  visitDictionaryLaws (dictionaries.toList.map (fun dictionary => (dictionary, []))) params models #[] k

private meta def bareConstant (stx : Syntax) : TermElabM Name := do
  let id ← match stx with
    | `(@$id:ident) => pure id
    | `($id:ident) => pure id
    | _ => throwErrorAt stx "Expected a bare extracted declaration"
  realizeGlobalConstNoOverloadWithInfo id

elab "trait_dictionary " raw:term:max : command => Command.liftTermElabM do
  let declName ← bareConstant raw
  if (traitLawExtension.getState (← getEnv)).contains declName then
    throwErrorAt raw "Duplicate extracted trait dictionary registration: {declName}"
  forallTelescope (← getConstInfo declName).type fun _ result => do
    unless result.isSort && result != mkSort .zero do
      throwErrorAt raw "An extracted trait dictionary must produce a Type"
  modifyEnv (traitLawExtension.addEntry · {raw := declName})

private meta def expressionText (expression : Expr) : TermElabM String := do
  return (← withOptions (fun options => (options.setBool `pp.explicit true)
      |>.setBool `pp.universes false) (ppExpr expression)).pretty 100000

private meta def parseDeclaration (text : String) : Command.CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .ok declaration => pure declaration
  | .error error => throwError "Generated trait law failed to parse: {error}\n{text}"

elab "trait_invariant " lawId:ident " for " raw:term:max " with " count:num
    " type " "parameters" " where " dictionaryId:ident " => " predicate:term : command => do
  let (rawName, binders, levels, modelParameters) ← Command.liftTermElabM do
    let rawName ← bareConstant raw
    let some binding ← traitDictionary? (mkConst rawName)
      | throwErrorAt raw "Trait invariant lacks an extracted dictionary registration"
    if binding.law.isSome then throwErrorAt raw "Duplicate trait invariant"
    let info ← getConstInfo rawName
    let (text, modelParameters) ← forallTelescope info.type fun params result => do
      unless params.size == count.getNat && result.isSort && result != mkSort .zero do
        throwErrorAt count "Trait invariant generic count disagrees with its extracted dictionary"
      let mut binders := ""
      let mut names : Array Name := #[]
      for parameter in params do
        let parameterName := (← parameter.fvarId!.getDecl).userName.eraseMacroScopes
        unless (← whnf (← inferType parameter)).isSort do
          throwErrorAt raw "Only Type-valued trait parameters are supported"
        if parameterName == dictionaryId.getId || names.contains parameterName then
          throwErrorAt dictionaryId "Trait invariant binder shadows a type parameter"
        names := names.push parameterName
        binders := binders ++ s!" ({parameterName} : {← expressionText (← inferType parameter)})"
      let carrier := mkAppN (← mkConstWithFreshMVarLevels rawName) params
      let originalBinders := binders ++ s!" ({dictionaryId.getId} : {← expressionText carrier})"
      withLocalDeclD dictionaryId.getId carrier fun _dictionary =>
        withModelDictionaries params fun models => do
          let expression ← elabTermEnsuringType predicate (mkSort .zero)
          synthesizeSyntheticMVarsNoPostponing
          let expression ← instantiateMVars expression
          let mut captured := #[]
          let mut suffix := ""
          for i in [:models.size] do
            if expression.containsFVar models[i]!.fvarId! then
              captured := captured.push i
              suffix := suffix ++ s!" [_rustModel{i} : {← expressionText (← inferType models[i]!)}]"
          pure (originalBinders ++ suffix, captured)
    pure (rawName, text, info.levelParams, modelParameters)
  -- Elaborate again with only the captured providers. The original native
  -- trait parameters and computational dictionary remain the exact prefix.
  let body := String.intercalate "\n"
    ((predicate.raw.reprint.getD "").splitOn "\n" |>.map (fun line => "    " ++ line))
  Command.withScope (fun scope => {scope with
      levelNames := levels ++ scope.levelNames
      opts := scope.opts.setBool `autoImplicit false}) do
    Command.elabCommand (← parseDeclaration
      s!"class {lawId.getId}{binders} : Prop where\n  holds :\n{body}")
  if ← MonadLog.hasErrors then return
  Command.liftTermElabM do
    let lawName ← realizeGlobalConstNoOverloadWithInfo lawId
    modifyEnv (traitLawExtension.addEntry · {raw := rawName, law := some lawName, modelParameters})

/-- Independently check the compiled class's original prefix and captured
provider indices. Every captured provider must occur in the authored predicate. -/
meta def checkTraitLawModelParameters (binding : TraitLawBinding) (typeCount : Nat)
    : MetaM Unit := do
  let some law := binding.law | throwError "Missing annotated trait law"
  forallTelescope (← getConstInfo law).type fun inputs _ => do
    unless inputs.size == typeCount + 1 + binding.modelParameters.size do
      throwError "Trait law changed its original dictionary/provider prefix"
    let mut seen : Array Nat := #[]
    let params := inputs.extract 0 typeCount
    let expectedCarrier := mkAppN (← mkConstWithFreshMVarLevels binding.raw) params
    unless ← isDefEq (← inferType inputs[typeCount]!) expectedCarrier do
      throwError "Trait law changed its exact computational dictionary"
    for i in [:binding.modelParameters.size] do
      let index := binding.modelParameters[i]!
      unless index < typeCount && !seen.contains index do
        throwError "Invalid or repeated captured trait model parameter"
      seen := seen.push index
      let expected ← mkAppM ``RustModel #[params[index]!]
      unless ← isDefEq (← inferType inputs[typeCount + 1 + i]!) expected do
        throwError "Trait law changed its captured RustModel index"
  forallTelescope (← getConstInfo (law ++ `holds)).type fun inputs predicate => do
    for i in [:binding.modelParameters.size] do
      unless predicate.containsFVar inputs[typeCount + 1 + i]!.fvarId! do
        throwError "Trait law captured an unused model provider"

/-- Compare the compiled implementation telescope with the pre/final native
binding inventory, including const names, positions, and usize types. -/
meta def checkTraitImplementationNativeParameters (implementation : Name)
    (typeCount constCount dictionaryCount : Nat) (constParameters : Array Json)
    : MetaM Unit := do
  unless constParameters.size == constCount do
    throwError "Trait implementation changed its original const inventory"
  forallTelescope (← getConstInfo implementation).type fun inputs _ => do
    unless inputs.size == typeCount + constCount + dictionaryCount do
      throwError "Trait implementation changed its original native parameter count"
    for input in inputs.extract 0 typeCount do
      unless (← whnf (← inferType input)).isSort do
        throwError "Trait implementation type parameter is not a native Type"
    for index in [:constCount] do
      let row := constParameters[index]!
      let .ok originalIndex := row.getObjValAs? Nat "index"
        | throwError "Missing original trait const index"
      let .ok originalName := row.getObjValAs? String "name"
        | throwError "Missing original trait const name"
      let .ok originalType := row.getObjValAs? String "type"
        | throwError "Missing original trait const type"
      let input := inputs[typeCount + index]!
      unless originalIndex == index && originalType == "usize" &&
          (← input.fvarId!.getDecl).userName.eraseMacroScopes.toString == originalName &&
          (← isDefEq (← inferType input) (mkConst ``Aeneas.Std.Usize)) do
        throwError "Trait implementation changed its original usize const binding"
    checkTraitDictionaryPrefix inputs (typeCount + constCount) dictionaryCount

/-- A concrete implementation's obligation quantifies its original native
inputs, the model indices actually used, and laws of input dictionaries. It
cannot acquire an arbitrary extra premise that simply assumes the implementation's own law.
-/
meta def traitImplementationObligation (law implementation : Name) : TermElabM Expr := do
  let implementationExpr ← mkConstWithFreshMVarLevels implementation
  forallTelescope (← inferType implementationExpr) fun inputs result => do
    let some binding ← traitDictionary? result
      | throwError "Implementation does not return an extracted trait dictionary"
    unless binding.law == some law do
      throwError "Implementation's exact trait dictionary has a different invariant"
    let mut dictionaries := #[]
    let mut params : Array Expr := #[]
    for input in inputs do
      let carrier ← inferType input
      if (← whnf carrier).isSort then params := params.push input
      else if (← traitDictionary? carrier).isSome then
        dictionaries := dictionaries.push input
      else if ← isDefEq carrier (mkConst ``Aeneas.Std.Usize) then pure ()
      else throwError "Unsupported non-dictionary implementation parameter: {carrier}"
    withModelDictionaries params fun models =>
      withTraitLawAssumptions dictionaries params models fun evidence => do
        let dictionary := mkAppN implementationExpr inputs
        let target ← traitLawProposition binding result dictionary params models
        -- Only providers actually used by the target or input laws are indices.
        -- In particular, an output law is never introduced as an assumption.
        let evidenceTypes ← evidence.mapM fun e => inferType e
        let used := models.filter fun provider =>
          target.containsFVar provider.fvarId! ||
            evidenceTypes.any (·.containsFVar provider.fvarId!)
        mkForallFVars (inputs ++ used ++ evidence) target

/-- The native implementation determines its witness name; no second roster
can omit an implementation while retaining its authored proof. -/
meta def traitImplementationWitnessName (implementation : Name) : Name :=
  implementation.appendAfter "_trait_law_checked"

/-- Inspect the compiled theorem independently of obligation generation.
Keep the native inputs, enumerate their parent projections, and inspect each
law application and provider directly. This deliberately does not call the
obligation or assumption builders used by the command below. -/
meta def auditTraitImplementationProof (law implementation proof : Name) : TermElabM Unit := do
  let .thmInfo proofInfo ← getConstInfo proof
    | throwError "Trait invariants require an ordinary checked Lean theorem"
  let native ← mkConstWithFreshMVarLevels implementation
  forallTelescope (← inferType native) fun original result =>
    forallTelescope proofInfo.type fun inputs conclusion => do
      unless original.size ≤ inputs.size do
        throwError "Trait implementation proof omitted original native inputs"
      let nativeInputs := inputs.extract 0 original.size
      let subst (e : Expr) := e.replaceFVars original nativeInputs
      for i in [:original.size] do
        unless ← isDefEq (← inferType nativeInputs[i]!) (subst (← inferType original[i]!)) do
          throwError "Trait implementation proof changed its native input prefix"
      let result := subst result
      let some output ← traitDictionary? result
        | throwError "Implementation must return an extracted trait dictionary"
      unless output.law == some law do
        throwError "Implementation returns a different annotated trait"
      let mut params := #[]
      let mut pending : List (Expr × List Name) := []
      for input in nativeInputs do
        let carrier ← inferType input
        if (← whnf carrier).isSort then params := params.push input
        else if (← traitDictionary? carrier).isSome then
          pending := pending ++ [(input, [])]
        else unless ← isDefEq carrier (mkConst ``Aeneas.Std.Usize) do
          throwError "Unsupported native trait implementation input"
      -- Use fresh placeholders for generic meanings, then require precisely
      -- the placeholders referenced by the actual input laws or conclusion.
      let rec providers (index : Nat) (models : Array Expr) : TermElabM Unit := do
        if index < params.size then
          withLocalDecl (Name.mkSimple s!"_auditModel{index}") .instImplicit
              (← mkAppM ``RustModel #[params[index]!]) fun provider =>
            providers (index + 1) (models.push provider)
        else do
          let inspect (binding : TraitLawBinding) (carrier dictionary : Expr) : MetaM Expr := do
            let some className := binding.law | throwError "Missing annotated law"
            let arguments := carrier.getAppArgs
            let mut meanings := #[]
            for modelIndex in binding.modelParameters do
              unless modelIndex < arguments.size do throwError "Invalid trait model index"
              meanings := meanings.push (← boundModelProvider arguments[modelIndex]! params models)
            mkAppOptM className ((arguments ++ #[dictionary] ++ meanings).map some)
          let target ← inspect output result (mkAppN native nativeInputs)
          let mut laws := #[]
          let mut queue := pending
          while !queue.isEmpty do
            let (dictionary, ancestors) := queue.head!
            queue := queue.tail!
            let carrier ← inferType dictionary
            let some binding ← traitDictionary? carrier | throwError "Missing input dictionary"
            if ancestors.contains binding.raw then throwError "Recursive parent dictionary"
            if binding.law.isSome then
              laws := laws.push ((← inspect binding carrier dictionary), carrier.getAppArgs.size)
            if let some structureInfo := getStructureInfo? (← getEnv) binding.raw then
              let mut parents := []
              for field in [:structureInfo.fieldNames.size] do
                let parent := mkProj binding.raw field dictionary
                if (← traitDictionary? (← inferType parent)).isSome then
                  parents := parents ++ [(parent, binding.raw :: ancestors)]
              queue := parents ++ queue
          let used := models.filter fun provider =>
            target.containsFVar provider.fvarId! || laws.any (fun entry => entry.1.containsFVar provider.fvarId!)
          unless inputs.size == nativeInputs.size + used.size + laws.size do
            throwError "Trait implementation proof omitted required inputs or added premises"
          let meanings := inputs.extract nativeInputs.size (nativeInputs.size + used.size)
          for i in [:used.size] do
            unless (← meanings[i]!.fvarId!.getDecl).binderInfo == .instImplicit &&
                (← isDefEq (← inferType meanings[i]!) (← inferType used[i]!)) do
              throwError "Trait implementation proof changed its generic model providers"
          let replace (e : Expr) := e.replaceFVars used meanings
          -- Do not unfold the law class: a true predicate still has to name
          -- its own class, original dictionary, and canonical model providers.
          let application (actual expected : Expr) (dictionaryIndex : Nat)
              (nativeOutput : Bool := false) : MetaM Unit := do
            let actual := actual.consumeMData
            let expected ← instantiateMVars (replace expected)
            unless actual.getAppFn.isConst &&
                actual.getAppFn.constName? == expected.getAppFn.constName? &&
                actual.getAppArgs.size == expected.getAppArgs.size do
              throwError "Trait implementation proof changed its exact law application"
            unless ← isDefEq actual.getAppFn expected.getAppFn do
              throwError "Trait implementation proof changed its law universes"
            let actualArgs := actual.getAppArgs
            let expectedArgs := expected.getAppArgs
            for i in [:expectedArgs.size] do
              unless ← isDefEq actualArgs[i]! expectedArgs[i]! do
                throwError "Trait implementation proof changed its dictionary or canonical provider"
              if i == dictionaryIndex then
                let actualDictionary ← if nativeOutput then pure actualArgs[i]!.consumeMData
                  else withTransparency .reducible (whnf actualArgs[i]!)
                let expectedDictionary ← if nativeOutput then pure expectedArgs[i]!.consumeMData
                  else withTransparency .reducible (whnf expectedArgs[i]!)
                unless actualDictionary == (← instantiateMVars expectedDictionary) do
                  throwError "Trait implementation proof names a different native dictionary"
              if dictionaryIndex < i then
                unless actualArgs[i]!.consumeMData == (← instantiateMVars expectedArgs[i]!).consumeMData do
                  throwError "Trait implementation proof replaced a canonical provider"
          for i in [:laws.size] do
            let premise := inputs[nativeInputs.size + used.size + i]!
            unless (← premise.fvarId!.getDecl).binderInfo == .instImplicit do
              throwError "Input dictionary laws must be instance premises"
            application (← inferType premise) laws[i]!.1 laws[i]!.2
          application conclusion target result.getAppArgs.size true
      providers 0 #[]

/-- Add a normal theorem declaration. Lean's kernel checks the authored proof
against the complete native obligation, independently of Meta.isDefEq. -/
meta def addTraitImplementationWitness (law implementation proof : Name) : TermElabM Unit := do
  let .thmInfo info ← getConstInfo proof
    | throwError "Trait invariants require an ordinary checked Lean theorem"
  let expected ← traitImplementationObligation law implementation
  -- Resolve universe metavariables before the closed kernel declaration.
  let value := Lean.mkConst proof (info.levelParams.map Level.param)
  let _ ← isDefEq (← inferType value) expected
  let witnessName := traitImplementationWitnessName implementation
  let declaration : TheoremVal :=
    ⟨⟨witnessName, info.levelParams, ← instantiateMVars expected⟩, value, [witnessName]⟩
  addDecl (.thmDecl declaration) (forceExpose := true)

elab "check_trait_law " law:term:max " for " implementation:term:max " using " proof:term:max
    : command => Command.liftTermElabM do
  let lawName ← bareConstant law
  let implementationName ← bareConstant implementation
  let proofName ← bareConstant proof
  let .thmInfo info ← getConstInfo proofName
    | throwErrorAt proof "Trait invariants require an ordinary checked Lean theorem"
  let expected ← traitImplementationObligation lawName implementationName
  unless ← isDefEq info.type expected do
    throwErrorAt proof "Trait implementation proof has the wrong dictionary, parameters, or premises\nExpected: {expected}\nActual: {info.type}"
  auditTraitImplementationProof lawName implementationName proofName
  addTraitImplementationWitness lawName implementationName proofName

end AeneasSpecs
