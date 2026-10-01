/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DeriveModels
public meta import Lean
public section

open Lean Aeneas Aeneas.Std
namespace AeneasSpecs

meta initialize specAttribute : TagAttribute ←
  registerTagAttribute `aeneas_spec "A transparent Aeneas specification"

declare_syntax_cat specRequirement
syntax "requires " ident " : " term : specRequirement
syntax "requires(raw) " ident " : " term : specRequirement

declare_syntax_cat specPostcondition
syntax "ensures " term+ " => " term : specPostcondition
syntax "ensures(raw) " term+ " => " term : specPostcondition

syntax (name := totalSpec) "spec " ident bracketedBinder* " for " term
  " with " num " type " "parameters" specRequirement* specPostcondition+ : command
syntax (name := partialSpec) "partial " "spec " ident bracketedBinder* " for " term
  " with " num " type " "parameters" specRequirement* specPostcondition+ : command

syntax (name := specBody) "aeneas_spec_body% " term " with " num " mode% " num
  " ghosts% " bracketedBinder* " requires% " specRequirement*
  " posts% " specPostcondition+ : term

private meta def checkFreshNames (previous : Array Expr) (newInputs : Array Expr)
    : Elab.Term.TermElabM Unit := do
  let mut names ← previous.mapM fun e => return (← e.fvarId!.getDecl).userName.eraseMacroScopes
  for input in newInputs do
    let binderName := (← input.fvarId!.getDecl).userName.eraseMacroScopes
    if names.contains binderName then
      throwError "Specification binder {binderName} shadows an original input or an earlier binder"
    names := names.push binderName

private meta partial def withOriginalInputs (carrier : Expr) (inputs : Array Expr)
    (k : Array Expr → Expr → Elab.Term.TermElabM Expr) : Elab.Term.TermElabM Expr := do
  match carrier with
  | .forallE binderName domain body _ =>
    Meta.withLocalDeclD binderName.eraseMacroScopes domain fun input => do
      checkFreshNames inputs #[input]
      withOriginalInputs (body.instantiate1 input) (inputs.push input) k
  | _ => k inputs carrier

/-- Clause scopes change only local declaration names. Authored terms elaborate
against exact free variables; no textual identifier replacement is performed. -/
private meta def withClauseScope (raws maths : Array Expr) (useRaw : Bool)
    (k : Elab.Term.TermElabM α) : Elab.Term.TermElabM α := withFreshMacroScope do
  let mut lctx ← getLCtx
  for i in [:raws.size] do
    let userName := (← raws[i]!.fvarId!.getDecl).userName
    let hiddenRaw ← MonadQuotation.addMacroScope (Name.mkSimple s!"_rawInput{i}")
    let hiddenMath ← MonadQuotation.addMacroScope (Name.mkSimple s!"_mathInput{i}")
    lctx := lctx.setUserName raws[i]!.fvarId! (if useRaw then userName else hiddenRaw)
    lctx := lctx.setUserName maths[i]!.fvarId! (if useRaw then hiddenMath else userName)
  Meta.withLCtx' lctx k

private meta partial def withDecodedInputs (raws providers : Array Expr) (i : Nat)
    (maths equations : Array Expr)
    (k : Array Expr → Array Expr → Elab.Term.TermElabM Expr) : Elab.Term.TermElabM Expr := do
  if h : i < raws.size then
    let raw := raws[i]
    let rawTy ← Meta.inferType raw
    let provider := providers[i]!
    let mathTy ← providerModel rawTy provider
    Meta.withLocalDeclD (Name.mkSimple s!"_mathInput{i}") mathTy fun math => do
      let equation ← Meta.mkEq (← providerDecode rawTy provider raw)
        (← Meta.mkAppM ``Option.some #[math])
      Meta.withLocalDeclD (Name.mkSimple s!"_decodedInput{i}") equation fun hDecoded =>
        withDecodedInputs raws providers (i+1) (maths.push math) (equations.push hDecoded) k
  else k maths equations

private meta partial def withRequirements (requirements : Array Syntax) (i : Nat)
    (raws maths previous : Array Expr)
    (k : Array Expr → Elab.Term.TermElabM Expr) : Elab.Term.TermElabM Expr := do
  if h : i < requirements.size then
    let (id, proposition, useRaw) ← match requirements[i] with
      | `(specRequirement| requires $id:ident : $pre:term) => pure (id, pre, false)
      | `(specRequirement| requires(raw) $id:ident : $pre:term) => pure (id, pre, true)
      | _ => throwError "Unexpected requirement: {repr requirements[i]}"
    let carrierType ← withClauseScope raws maths useRaw
      (Elab.Term.elabTermEnsuringType proposition (mkSort .zero))
    Meta.withLocalDeclD id.getId carrierType fun hypothesis => do
      checkFreshNames previous #[hypothesis]
      withRequirements requirements (i+1) raws maths (previous.push hypothesis) k
  else k previous

/-- Use upstream result-pattern notation, retaining ordinary Lean ascriptions
and tuple patterns in either raw or mathematical result scope. -/
private meta def patternPredicate (patterns : Array (TSyntax `term))
    (body : TSyntax `term) : Elab.Term.TermElabM (TSyntax `term) := do
  let contract ← match patterns.toList with
    | [binder] => `(Result.ok () ⦃ $binder => $body ⦄)
    | binder :: rest => do
      let tail := rest.toArray
      `(Result.ok () ⦃ $binder $tail:term* => $body ⦄)
    | [] => throwError "A result pattern is required"
  let some expanded ← Elab.liftMacroM (expandMacro? contract.raw) | throwError "Unsupported result pattern"
  match expanded with
  | `(Aeneas.Std.WP.spec $_call $post) => pure post
  | _ => throwError "Unsupported upstream result-pattern expansion"

private meta def postcondition (posts : Array Syntax) (raws maths : Array Expr)
    (rawType provider : Expr) : Elab.Term.TermElabM Expr := do
  Meta.withLocalDeclD `_rawOutput rawType fun raw => do
    let mathType ← providerModel rawType provider
    Meta.withLocalDeclD `_mathOutput mathType fun math => do
      let mut propositions := #[]
      for post in posts do
        unless post.getNumArgs == 4 && #["ensures", "ensures(raw)"].contains post[0].getAtomVal do
          throwError "Malformed specification postcondition"
        let patterns : Array (TSyntax `term) := post[1].getArgs.map (fun stx => ⟨stx⟩)
        let body : TSyntax `term := ⟨post[3]⟩
        let useRaw := post[0].getAtomVal == "ensures(raw)"
        let predicateSyntax ← patternPredicate patterns body
        let carrierType ← mkArrow (if useRaw then rawType else mathType) (mkSort .zero)
        let predicate ← withClauseScope raws maths useRaw
          (Elab.Term.elabTermEnsuringType predicateSyntax carrierType)
        propositions := propositions.push (mkApp predicate (if useRaw then raw else math))
      let mut conjunction := propositions.back!
      for p in (propositions.extract 0 (propositions.size-1)).reverse do
        conjunction ← Meta.mkAppM ``And #[p, conjunction]
      let equation ← Meta.mkEq (← providerDecode rawType provider raw)
        (← Meta.mkAppM ``Option.some #[math])
      let body ← Meta.mkAppM ``And #[equation, conjunction]
      let existsExpr ← Meta.mkAppM ``Exists #[← Meta.mkLambdaFVars #[math] body]
      Meta.mkLambdaFVars #[raw] existsExpr

@[term_elab specBody] meta def elabSpecBody : Elab.Term.TermElab := fun stx _ => do
  match stx with
  | `(aeneas_spec_body% $function:term with $count:num mode% $mode:num
      ghosts% $ghosts:bracketedBinder* requires% $requirements:specRequirement*
      posts% $posts:specPostcondition*) =>
    let id ← match function with
      | `(@$id:ident) => pure id
      | `($id:ident) => pure id
      | _ => throwErrorAt function "A specification must name a bare extracted function constant"
    let functionName ← Elab.realizeGlobalConstNoOverloadWithInfo id
    let functionExpr ← Meta.mkConstWithFreshMVarLevels functionName
    withOriginalInputs (← Meta.inferType functionExpr) #[] fun originals returnType => do
      unless count.getNat ≤ originals.size do throwErrorAt count "Invalid Rust type-parameter prefix"
      for input in originals[:count.getNat] do
        let carrierType ← Meta.whnf (← Meta.inferType input)
        unless carrierType.isSort && carrierType != mkSort .zero do
          throwErrorAt count "Rust generic parameters must be the original Type-valued prefix"
      for input in originals[count.getNat:] do
        if (← Meta.whnf (← Meta.inferType input)).isSort then
          throwErrorAt count "Rust type-parameter count omits an original type parameter"
      let returnType ← Meta.whnf returnType
      unless returnType.isAppOfArity ``Result 1 do
        throwErrorAt function "Extracted function must return an Aeneas execution Result"
      let rawOutputType := returnType.appArg!
      let params := originals.extract 0 count.getNat
      let raws := originals.extract count.getNat originals.size
      let inputNames ← raws.mapM fun raw => return (← raw.fvarId!.getDecl).userName
      withModelDictionaries params fun dictionaries => do
        -- Fix all automatic providers before introducing decoded witnesses,
        -- dependent ghosts, requirements, or their local instances.
        let providers ← raws.mapM fun raw => do
          boundModelProvider (← Meta.inferType raw) params dictionaries
        let outputProvider ← boundModelProvider rawOutputType params dictionaries
        withDecodedInputs raws providers 0 #[] #[] fun maths equations => do
          let decodedPrefix := (maths.zip equations).foldl
            (fun inputs pair => inputs ++ #[pair.1, pair.2]) #[]
          let boundPrefix := originals ++ dictionaries ++ decodedPrefix
          withClauseScope raws maths false <| Elab.Term.elabBinders ghosts fun ghostInputs => do
            -- Restore raw names as the baseline for each clause-specific scope.
            let mut lctx ← getLCtx
            for i in [:raws.size] do
              lctx := lctx.setUserName raws[i]!.fvarId! inputNames[i]!
              lctx := lctx.setUserName maths[i]!.fvarId! (Name.mkSimple s!"_mathInput{i}")
            Meta.withLCtx' lctx do
              checkFreshNames boundPrefix ghostInputs
              withRequirements requirements 0 raws maths (boundPrefix ++ ghostInputs) fun inputs => do
                let post ← postcondition posts raws maths rawOutputType outputProvider
                let call := mkAppN functionExpr originals
                let wp := if mode.getNat == 0 then ``WP.spec else ``WP.dspec
                let body ← Meta.mkAppM wp #[call, post]
                Elab.Term.synthesizeSyntheticMVarsNoPostponing
                Elab.Term.levelMVarToParam (← Meta.mkForallFVars inputs (← instantiateMVars body))
  | _ => throwError "Unexpected specification syntax: {repr stx}"

private meta def expandSpec (id : TSyntax `ident)
    (ghosts : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (function : TSyntax `term) (count : TSyntax `num) (isPartial : Bool)
    (requirements : Array (TSyntax `specRequirement))
    (posts : Array (TSyntax `specPostcondition)) : MacroM Syntax := do
  let mode := Syntax.mkNumLit (if isPartial then "1" else "0")
  let body ← `(aeneas_spec_body% $function with $count mode% $mode:num
    ghosts% $ghosts:bracketedBinder* requires% $requirements:specRequirement* posts% $posts:specPostcondition*)
  `(set_option linter.unusedVariables false in
    @[aeneas_spec] abbrev $id : Prop := $body)

macro_rules
  | `(spec $id:ident $ghosts:bracketedBinder* for $function:term with $count:num type parameters
      $requirements:specRequirement* $posts:specPostcondition*) =>
    expandSpec id ghosts function count false requirements posts
  | `(partial spec $id:ident $ghosts:bracketedBinder* for $function:term with $count:num type parameters
      $requirements:specRequirement* $posts:specPostcondition*) =>
    expandSpec id ghosts function count true requirements posts

syntax "aeneas_spec_begin " command " aeneas_spec_end" : command
macro_rules
  | `(aeneas_spec_begin $declaration:command aeneas_spec_end) => do
    unless #[``totalSpec, ``partialSpec].contains declaration.raw.getKind do
      Macro.throwErrorAt declaration "An Aeneas fence must contain exactly one spec declaration"
    pure declaration.raw

/-- Read a specification's actual model call without reducing the application.
Each argument must be its original prefix input variable; ghost inputs and
requirements may follow that prefix. Both the generated command and the final
coverage audit use this same elaborated-expression check. -/
meta def specBinding (specName : Name) : MetaM (Name × Nat) := do
  let info ← getConstInfo specName
  let .defnInfo declaration := info
    | throwError "Expected a specification declaration, got {specName}"
  unless specAttribute.hasTag (← getEnv) specName do
    throwError "Expected a specification declaration, got {specName}"
  Meta.forallTelescope declaration.value fun inputs body => do
    let body := body.consumeMData
    unless body.getAppFn.isConstOf ``WP.spec || body.getAppFn.isConstOf ``WP.dspec do
      throwError "Specification {specName} does not directly state a total or partial contract"
    let contractArgs := body.getAppArgs
    unless contractArgs.size == 3 do
      throwError "Specification {specName} has an unexpected contract application"
    let call := contractArgs[1]!.consumeMData
    let .const modelName _ := call.getAppFn
      | throwError "Specification {specName} does not directly call a model declaration"
    let arguments := call.getAppArgs
    unless inputs.size ≥ arguments.size do
      throwError "Specification {specName} has more model arguments than bound inputs"
    for index in [:arguments.size] do
      unless arguments[index]!.consumeMData == inputs[index]! do
        throwError "Specification {specName} model input {index + 1} is not its original bound variable"
    pure (modelName, arguments.size)

/-- Check the actual call against the independently verified model declaration
and Rust type/value parameter count supplied by the generated command. -/
elab "check_spec_binding " candidate:ident " for " extractedId:ident " with " count:num : command =>
    Elab.Command.liftTermElabM do
  let specName ← Elab.realizeGlobalConstNoOverloadWithInfo candidate
  let modelName ← Elab.realizeGlobalConstNoOverloadWithInfo extractedId
  let (actualModel, inputCount) ← withRef candidate (specBinding specName)
  unless actualModel == modelName do
    throwErrorAt candidate "Specification {specName} does not call the expected model {modelName}"
  unless inputCount == count.getNat do
    throwErrorAt candidate "Specification {specName} does not bind exactly {count.getNat} model inputs"

/-- Register an ordinary theorem whose type names a `spec` proposition with
Aeneas's existing step database. This pinned upstream registry inspects theorem
types syntactically. The generated alias expands only specifications, and Lean
checks its original theorem value against the expanded type. -/
elab "register_spec_step " candidate:ident : command => Elab.Command.liftCoreM do
  let thmName ← Elab.realizeGlobalConstNoOverloadWithInfo candidate
  let info ← getConstInfo thmName
  let .thmInfo _ := info
    | throwError "Expected a theorem, got {thmName}"
  let env ← getEnv
  let expanded ← Meta.deltaExpand info.type (specAttribute.hasTag env)
  let adapterName := thmName.appendAfter "_step"
  let declaration : TheoremVal := ⟨⟨adapterName, info.levelParams, expanded⟩,
    mkConst thmName (info.levelParams.map Level.param), [adapterName]⟩
  addDecl (.thmDecl declaration)
  Elab.addDeclarationRangesFromSyntax adapterName candidate
  Attribute.add adapterName `step .missing .global

end AeneasSpecs
