/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustModel
public meta import Lean
public section

/-!
Native definitions retain their original arguments while section-variable
capture supplies only the model providers their elaborated bodies use. Every
original argument occurs in an anonymous let around the unchanged source body;
these lets preserve otherwise-unused arguments and reduce to that body.
The supported input is the native generator's named, typed binder groups and
nonrecursive `:=` declarations without auxiliary declarations.
-/

open Lean Meta Elab Command
namespace AeneasSpecs

private meta def nativeModelRaw? (input : Expr) : MetaM (Option Expr) := do
  let type ← whnf (← inferType input)
  if type.getAppFn.isConstOf ``RustModel && type.getAppArgs.size == 1 then
    return some type.getAppArgs[0]!
  return none

/-- Split the original Rust argument prefix from its canonical model suffix.
Models must be instance arguments for distinct original type variables, in
their original order. A container model or an independently equal type cannot
stand in for the exact original variable.
-/
meta def splitNativeModels (inputs : Array Expr) :
    MetaM (Array Expr × Array Expr) := do
  for input in inputs do
    unless input.isFVar do
      throwError "Native model arguments require local telescope variables"
  let mut firstModel := inputs.size
  while firstModel > 0 do
    if (← nativeModelRaw? inputs[firstModel - 1]!).isNone then break
    firstModel := firstModel - 1
  let original := inputs.extract 0 firstModel
  let models := inputs.extract firstModel inputs.size
  for input in original do
    if (← nativeModelRaw? input).isSome then
      throwError "Native RustModel arguments must form a trailing suffix"
  let mut previous : Option Nat := none
  for model in models do
    unless (← model.fvarId!.getDecl).binderInfo.isInstImplicit do
      throwError "Native RustModel suffix arguments must be instance implicit"
    let some raw ← nativeModelRaw? model
      | throwError "Missing native RustModel argument"
    unless raw.isFVar do
      throwError "Native models require an exact original type variable"
    let mut position : Option Nat := none
    for index in [:original.size] do
      if original[index]! == raw then position := some index
    let some index := position
      | throwError "Native model type is not an original argument"
    let .sort level ← whnf (← inferType raw)
      | throwError "Native models require Type-valued original arguments"
    if level.isZero then
      throwError "Native models require Type-valued original arguments"
    if previous.any (· >= index) then
      throwError "Native model suffix must follow original type order without duplicates"
    previous := some index
  return (original, models)

private meta def nativeBinderNames (binder : Syntax) :
    CommandElabM (Array (TSyntax `ident) × Bool) := do
  let (names, type) ← if binder.isOfKind ``Parser.Term.explicitBinder ||
      binder.isOfKind ``Parser.Term.implicitBinder then do
    unless binder[2].getNumArgs == 2 &&
        (!binder.isOfKind ``Parser.Term.explicitBinder || binder[3].isNone) do
      throwErrorAt binder "native_models requires typed binders without defaults"
    pure (binder[1].getArgs, (⟨binder[2][1]⟩ : TSyntax `term))
  else if binder.isOfKind ``Parser.Term.instBinder then do
    unless binder[1][0].isIdent do
      throwErrorAt binder "native_models requires named instance arguments"
    pure (#[binder[1][0]], (⟨binder[2]⟩ : TSyntax `term))
  else throwErrorAt binder
        "native_models requires named, typed explicit, implicit, or instance binders"
  let names ← names.mapM fun binderId => do
    unless binderId.isIdent do
      throwErrorAt binderId "native_models does not support anonymous arguments"
    pure (⟨binderId⟩ : TSyntax `ident)
  let isType := match type with
    | `(Type) => true
    | _ => false
  return (names, isType)

elab mods:declModifiers "native_models " "def " id:declId
    sig:optDeclSig val:declVal : command => do
  -- Native output has no declaration-local universe binder or equation/where
  -- declarations. Reject them rather than relocating their binding scopes.
  unless id.raw[1].getArgs.isEmpty do
    throwErrorAt id "native_models does not support declaration-local universes"
  let `(declVal| := $body) := val
    | throwErrorAt val "native_models requires a plain := body"
  let binders := sig.raw[0].getArgs
  let mut names : Array (TSyntax `ident) := #[]
  let mut types : Array (TSyntax `ident) := #[]
  for binder in binders do
    let (bound, isType) ← nativeBinderNames binder
    for binderId in bound do
      if names.any (·.getId == binderId.getId) then
        throwErrorAt binderId "native_models requires distinct argument names"
      names := names.push binderId
      if isType then types := types.push binderId
  Command.withScope (fun scope => scope) do
    if !binders.isEmpty then
      let binders := binders.map (fun binder =>
        (⟨binder⟩ : TSyntax ``Parser.Term.bracketedBinder))
      elabCommand (← `(command| variable $binders*))
    let mut occupied := names
    for type in types do
      let mut index := 0
      let mut provider := mkIdent <| Name.mkSimple s!"_nativeModel{index}"
      while occupied.any (·.getId == provider.getId) do
        index := index + 1
        provider := mkIdent <| Name.mkSimple s!"_nativeModel{index}"
      occupied := occupied.push provider
      elabCommand (← `(variable [$provider : AeneasSpecs.RustModel $type]))
    let mut retained : TSyntax `term := ⟨body.raw⟩
    for binderId in names.reverse do
      -- Explicit application also retains higher-rank arguments without
      -- inserting their own implicit inputs or instance arguments.
      let arg : TSyntax `term :=
        ⟨mkNode ``Parser.Term.explicit #[mkAtom "@", binderId.raw]⟩
      retained ← `(term| let _ := $arg; $retained)
    let sig : TSyntax ``Parser.Command.optDeclSig :=
      ⟨sig.raw.setArg 0 (mkNullNode #[])⟩
    let val : TSyntax ``Parser.Command.declVal :=
      ⟨val.raw.setArg 1 retained.raw⟩
    let definition := mkNode ``Parser.Command.definition #[
      mkAtom "def", id.raw, sig.raw, val.raw, mkNullNode #[]]
    elabCommand (mkNode ``Parser.Command.declaration #[mods.raw, definition])

end AeneasSpecs
