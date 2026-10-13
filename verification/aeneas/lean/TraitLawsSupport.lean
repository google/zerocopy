/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
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

structure TraitLawBinding where
  raw : Name
  law : Option Name := none
  deriving Inhabited

private meta initialize traitLawExtension :
    SimplePersistentEnvExtension TraitLawBinding (NameMap TraitLawBinding) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state binding => state.insert binding.raw binding
    addImportedFn := fun entries => entries.foldl (fun state bindings =>
      bindings.foldl (fun state binding => state.insert binding.raw binding) state) {}
  }

meta def traitLawBindings : MetaM (Array TraitLawBinding) := do
  return ((traitLawExtension.getState (← getEnv)).toList.map (·.2)).toArray

meta def traitDictionary? (carrier : Expr) : MetaM (Option TraitLawBinding) := do
  let carrier := carrier.consumeMData
  let .const raw _ := carrier.getAppFn | return none
  return (traitLawExtension.getState (← getEnv)).find? raw

/-- Check the generated dictionary prefix against the actual function type.
Dictionary arguments are computational inputs, but they are not stored Rust
values and must not be decoded as if they were function value arguments. -/
meta def checkTraitDictionaryPrefix (inputs : Array Expr) (types dictionaries : Nat)
    : MetaM Unit := do
  unless types + dictionaries ≤ inputs.size do
    throwError "Invalid extracted trait-dictionary prefix"
  for input in inputs.extract types (types + dictionaries) do
    unless (← traitDictionary? (← inferType input)).isSome do
      throwError "Expected an original extracted trait dictionary, got {← inferType input}"
  for input in inputs.extract (types + dictionaries) inputs.size do
    if (← traitDictionary? (← inferType input)).isSome then
      throwError "Extracted trait-dictionary count omits an original dictionary"

/-- Native dictionary types identify their own prefix. The count in the
Rust binding manifest is checked separately against the compiled specification;
no extra source syntax is needed to tell Lean which arguments are dictionaries.
-/
meta def traitDictionaryCount (inputs : Array Expr) (types : Nat) : MetaM Nat := do
  unless types ≤ inputs.size do throwError "Invalid original Rust type prefix"
  let mut finish := types
  while finish < inputs.size do
    if (← traitDictionary? (← inferType inputs[finish]!)).isSome then
      finish := finish + 1
    else break
  let count := finish - types
  checkTraitDictionaryPrefix inputs types count
  return count

/-- Introduce laws for original dictionaries and their actual parent dictionary
fields. Parent projections preserve identity: a Child bound supplies the law
for that Child's Parent dictionary, not for an unrelated Parent implementation.
The generated assumptions are ordinary Lean instance binders, usable by step.
-/
private meta partial def visitDictionaryLaws (pending : List (Expr × List Name))
    (laws : Array Expr) (k : Array Expr → TermElabM α) : TermElabM α := do
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
    | none => visitDictionaryLaws next laws k
    | some law =>
      let proposition ← mkAppOptM law ((carrier.getAppArgs.push dictionary).map some)
      unless ← isProp proposition do
        throwError "Trait invariant is not a proposition: {law}"
      withLocalDecl (Name.mkSimple s!"_traitLaw{laws.size}") .instImplicit
          proposition fun evidence => visitDictionaryLaws next (laws.push evidence) k
meta def withTraitLawAssumptions (dictionaries : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  visitDictionaryLaws (dictionaries.toList.map (fun dictionary => (dictionary, []))) #[] k

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
  let (rawName, binders, levels) ← Command.liftTermElabM do
    let rawName ← bareConstant raw
    let some binding ← traitDictionary? (mkConst rawName)
      | throwErrorAt raw "Trait invariant lacks an extracted dictionary registration"
    if binding.law.isSome then throwErrorAt raw "Duplicate trait invariant"
    let info ← getConstInfo rawName
    let text ← forallTelescope info.type fun parameters result => do
      unless parameters.size == count.getNat && result.isSort && result != mkSort .zero do
        throwErrorAt count "Trait invariant generic count disagrees with its extracted dictionary"
      let mut binders := ""
      let mut names : Array Name := #[]
      for parameter in parameters do
        let parameterName := (← parameter.fvarId!.getDecl).userName.eraseMacroScopes
        unless (← whnf (← inferType parameter)).isSort do
          throwErrorAt raw "Only Type-valued trait parameters are supported"
        if parameterName == dictionaryId.getId || names.contains parameterName then
          throwErrorAt dictionaryId "Trait invariant binder shadows a type parameter"
        names := names.push parameterName
        binders := binders ++ s!" ({parameterName} : {← expressionText (← inferType parameter)})"
      let carrier := mkAppN (← mkConstWithFreshMVarLevels rawName) parameters
      pure (binders ++ s!" ({dictionaryId.getId} : {← expressionText carrier})")
    pure (rawName, text, info.levelParams)
  -- Lean elaborates the authored predicate as a Prop field. The generated
  -- declaration only supplies the original trait telescope and dictionary.
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
    modifyEnv (traitLawExtension.addEntry · {raw := rawName, law := some lawName})

/-- A concrete implementation's obligation quantifies only its original type
and dictionary inputs, plus laws of those input dictionaries. It cannot acquire
an arbitrary extra premise that simply assumes the implementation's own law.
-/
meta def traitImplementationObligation (law implementation : Name) : TermElabM Expr := do
  let implementationExpr ← mkConstWithFreshMVarLevels implementation
  forallTelescope (← inferType implementationExpr) fun inputs result => do
    let some binding ← traitDictionary? result
      | throwError "Implementation does not return an extracted trait dictionary"
    unless binding.law == some law do
      throwError "Implementation's exact trait dictionary has a different invariant"
    let mut dictionaries := #[]
    for input in inputs do
      let carrier ← inferType input
      if (← whnf carrier).isSort then pure ()
      else if (← traitDictionary? carrier).isSome then
        dictionaries := dictionaries.push input
      else throwError "Unsupported non-dictionary implementation parameter: {carrier}"
    withTraitLawAssumptions dictionaries fun evidence => do
      let dictionary := mkAppN implementationExpr inputs
      let target ← mkAppOptM law ((result.getAppArgs.push dictionary).map some)
      mkForallFVars (inputs ++ evidence) target

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

end AeneasSpecs
