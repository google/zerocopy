/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import DeriveModels
public meta import Lean
public section

/-!
An extracted function can receive more than one mathematical interpretation of
the same Lean type. Checking that a provider has the right *type* would therefore
miss a caller that passes the destination's interpretation for the source.

This audit follows each provider-bearing call back to its compiler identity and
ordered Rust type arguments. It compares the actual type variables and provider
expressions, before reducing them. The static assertion's global initializer is
also a function: omitting it would leave its size queries unaudited.

Only the type expressions exercised by these native calls are supported here.
A new expression needs an explicit extension; it cannot fall back to equality
of erased Lean carriers. Functional proofs and this binding audit serve different
purposes: a proof about the wrong provider can be perfectly valid Lean.
-/

open Lean Meta Elab AeneasSpecs

private meta def boundaryDefinition (declName : Name) (expected : TSyntax `term)
    (binders : Array BinderInfo) : TermElabM Unit := do
  let body ← Term.elabTerm expected none
  Term.synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  let some (.defnInfo actual) := (← getEnv).find? declName
    | throwError "Byte-copy boundary {declName} must be a definition"
  unless actual.levelParams.isEmpty && (← isDefEq actual.type (← inferType body)) &&
      (← isDefEq actual.value body) do
    throwError "Byte-copy boundary {declName} changed its whole signature or interpretation"
  forallTelescope actual.type fun inputs _ => do
    let actualBinders ← inputs.mapM fun input => return (← input.fvarId!.getDecl).binderInfo
    unless actualBinders == binders do
      throwError "Byte-copy boundary {declName} changed its argument binders"

private meta def providerAt (raw : Expr) (params models : Array Expr) : MetaM Expr :=
  boundModelProvider raw params models

private meta partial def originalType (text : String) (params : Array Expr) : MetaM Expr := do
  if text.startsWith "T" then
    if let some index := (text.drop 1).toString.toNat? then
      if let some rawTy := params[index]? then return rawTy
  if text == "usize" then return mkConst ``Aeneas.Std.Usize
  if text == "u32" then return mkConst ``Aeneas.Std.U32
  let wrapper := "core::mem::manually_drop::ManuallyDrop<"
  if text.startsWith wrapper && text.endsWith ">" then
    let child := ((text.drop wrapper.length).toString.dropEnd 1).toString
    return mkApp (mkConst ``core.mem.manually_drop.ManuallyDrop) (← originalType child params)
  throwError "Unsupported original type expression in provider-bearing call: {text}"

private meta partial def callsTo (names : Array Name) (expression : Expr) : Array Expr :=
  if expression.getAppFn.isConst && names.contains expression.getAppFn.constName! then
    #[expression] ++ expression.getAppArgs.foldl
      (fun calls arg => calls ++ callsTo names arg) #[]
  else
    match expression with
    | .app fn arg => callsTo names fn ++ callsTo names arg
    | .lam _ ty body _ | .forallE _ ty body _ => callsTo names ty ++ callsTo names body
    | .letE _ ty value body _ =>
      callsTo names ty ++ callsTo names value ++ callsTo names body
    | .mdata _ body | .proj _ _ body => callsTo names body
    | _ => #[]

private meta def typeInputs (inputs : Array Expr) : MetaM (Array Expr) :=
  inputs.filterM fun input => do
    match ← whnf (← inferType input) with
    | .sort level => return !level.isZero
    | _ => return false

private meta def jsonArray (json : Json) (key : String) : MetaM (Array Json) := do
  let .ok value := json.getObjValAs? (Array Json) key
    | throwError "Native provider audit lacks {key}"
  return value

private meta def jsonNat (json : Json) (key : String) : MetaM Nat := do
  let .ok value := json.getObjValAs? Nat key
    | throwError "Native provider audit lacks numeric {key}"
  return value

private meta def jsonName (json : Json) : MetaM Name := do
  let .ok value := json.getObjValAs? String "lean_name"
    | throwError "Native provider audit lacks compiled name"
  return value.toName

/-- Match every retained provider, including those forwarded through constants
and ordinary callers. Missing, extra, duplicated, or reordered calls fail. -/
meta def auditNativeProviders (bindings : Json) : TermElabM Unit := do
  let env ← getEnv
  let carrier := ``core.mem.manually_drop.ManuallyDrop
  let some shape := getStructureInfo? env carrier
    | throwError "ManuallyDrop must retain its nominal stored-value carrier"
  let .inductInfo carrierInfo ← getConstInfo carrier
    | throwError "ManuallyDrop must retain its nominal stored-value carrier"
  unless carrierInfo.levelParams.isEmpty && carrierInfo.numParams == 1 &&
      carrierInfo.numIndices == 0 && carrierInfo.ctors == [carrier ++ `mk] &&
      shape.fieldNames == #[`value] do
    throwError "ManuallyDrop changed its stored-value carrier"
  boundaryDefinition `AeneasSpecs.modelManuallyDrop
    (← `(fun (T : Type) [child : AeneasSpecs.RustModel T] =>
      ({ Model := child.Model, «decode» := fun raw => child.decode raw.value,
         storage := child.storage.map (fun physical => physical.map
           core.mem.manually_drop.ManuallyDrop.mk (fun raw => raw.value) (fun _ => rfl)),
         representationChoice := fun raw => child.representationChoice raw.value } :
        AeneasSpecs.RustModel (core.mem.manually_drop.ManuallyDrop T))))
    #[.default, .instImplicit]
  -- A native constructor and its nominal carrier preserve the payload. None
  -- of these definitions grants permission to read a dropped payload.
  boundaryDefinition `core.mem.manually_drop.ManuallyDrop.new
    (← `(fun {T : Type} (src : T) =>
      (Aeneas.Std.Result.ok (core.mem.manually_drop.ManuallyDrop.mk src))))
    #[.implicit, .default]
  boundaryDefinition `core.mem.transmute_copy
    (← `(fun {Src : Type} (Dst : Type) (src : Src)
      [source : AeneasSpecs.RustModel Src] [destination : AeneasSpecs.RustModel Dst] =>
      source.transmuteCopyResult destination src))
    #[.implicit, .default, .default, .instImplicit, .instImplicit]
  boundaryDefinition `AeneasSpecs.RustModel.sameSize
    (← `(fun (Src Dst : Type) [source : AeneasSpecs.RustModel Src]
      [destination : AeneasSpecs.RustModel Dst] =>
      ∃ width : Aeneas.Std.Usize,
        core.mem.size_of Src = .ok width ∧ core.mem.size_of Dst = .ok width ∧
        source.representation.map (·.byteSize) = some width.val ∧
        destination.representation.map (·.byteSize) = some width.val))
    #[.default, .default, .instImplicit, .instImplicit]
  let .ok admission := bindings.getObjVal? "admission"
    | throwError "Native provider audit requires compiler admission"
  let .ok stages := admission.getObjVal? "stages"
    | throwError "Native provider audit requires both compiler stages"
  let .ok before := stages.getObjVal? "before"
    | throwError "Native provider audit lacks original compiler stage"
  let .ok lowered := stages.getObjVal? "llbc"
    | throwError "Native provider audit lacks final compiler stage"
  let beforeCalls ← jsonArray before "calls"
  let loweredCalls ← jsonArray lowered "calls"
  let text ← IO.FS.readFile "Zerocopy/translation.json"
  let .ok native := Json.parse text | throwError "Invalid native provider map"
  let functions ← jsonArray native "functions"
  let globals ← jsonArray native "globals"
  let snapshot ← IO.FS.readFile "zerocopy.llbc"
  let .ok snapshot := Json.parse snapshot | throwError "Invalid compiler provider snapshot"
  let .ok crate := snapshot.getObjVal? "translated"
    | throwError "Missing compiler provider crate"
  let globalDecls ← jsonArray crate "global_decls"
  let mut owners : Array (Nat × Name) := #[]
  let mut targets : Array (Nat × Name) := #[]
  for row in functions do
    let compiledName ← jsonName row
    let ident ← jsonNat row "def_id"
    let .ok isOpaque := row.getObjValAs? Bool "is_opaque"
      | throwError "Native provider owner lacks its body disposition"
    -- Opaque rows name upstream templates, which need not be emitted at that
    -- name in our handwritten external module. Their complete interpretations
    -- have separate audits. Only these reviewed primitive endpoints seed
    -- semantic capture; every emitted native body is inspected below.
    if isOpaque && !#[`core.mem.zeroed, `core.mem.transmute_copy,
        `core.mem.size_of].contains compiledName then continue
    if !isOpaque then owners := owners.push (ident, compiledName)
    let info ← getConstInfo compiledName
    let semantic ← forallTelescope info.type fun inputs _ => do
      return (← splitNativeModels inputs).2.size
    if semantic > 0 || compiledName == `core.mem.size_of then
      targets := targets.push (ident, compiledName)
  for row in globals do
    let globalId ← jsonNat row "def_id"
    let compiledName ← jsonName row
    let matching := globalDecls.filter fun declaration =>
      declaration.getObjValAs? Nat "def_id" == .ok globalId
    unless matching.size == 1 do throwError "Global initializer has no unique compiler owner"
    -- A Charon named constant stores its initializer as a typed constant call,
    -- rather than exposing the initializer in Aeneas's function inventory.
    let initializer := do
      let value ← matching[0]!.getObjVal? "value"
      let typed ← value.getObjValAs? (Array Json) "Untagged"
      let call ← typed[0]!.getObjValAs? (Array Json) "Call"
      let kind ← call[0]!.getObjVal? "kind"
      kind.getObjValAs? Nat "Fun"
    let .ok ident := initializer
      | throwError "Native global has no supported compiler initializer"
    owners := owners.push (ident, compiledName)
    let (semantic, parameterCount) ← forallTelescope (← getConstInfo compiledName).type fun inputs _ => do
      let (original, models) ← splitNativeModels inputs
      return (models.size, (← typeInputs original).size)
    -- A monomorphic constant has no type/provider arguments to bind. Its
    -- initializer is still an owner, so every size read inside it is checked.
    -- Generic size constants, including StaticAssert, also need their uses
    -- checked so callers cannot substitute different endpoint types.
    if semantic > 0 || parameterCount > 0 && loweredCalls.any (fun call =>
        call.getObjValAs? Nat "caller_def_id" == .ok ident &&
        call.getObjValAs? String "callee" == .ok "core::mem::size_of") then
      targets := targets.push (ident, compiledName)
  let ids := targets.map Prod.fst
  let relevant := fun rows => rows.filter fun row =>
    (row.getObjValAs? Nat "callee_def_id").toOption.any ids.contains
  -- Aeneas shares identical pure size reads within the static assertion.
  -- Retain the full compiler inventory, but compare one binding per identical
  -- endpoint for this one audited read-only operation. Conversion calls keep
  -- their multiplicity, since each could make a different byte choice.
  let uniqueSizes := fun rows => rows.foldl (fun (seen : Array Json) row =>
    if row.getObjValAs? String "callee" == .ok "core::mem::size_of" && seen.contains row
    then seen else seen.push row) #[]
  let expected := uniqueSizes (relevant loweredCalls)
  unless uniqueSizes (relevant beforeCalls) == expected do
    throwError "Provider-bearing calls changed original endpoints, owners, or multiplicity"
  let mut remaining := expected
  for (ownerId, ownerName) in owners do
    let some (.defnInfo owner) := (← getEnv).find? ownerName
      | throwError "Native provider owner {ownerName} must retain its body"
    remaining ← lambdaTelescope owner.value fun inputs body => do
      let (originals, models) ← splitNativeModels inputs
      let params ← typeInputs originals
      let mut found := callsTo (targets.map Prod.snd) body
      for input in inputs do found := found ++ callsTo (targets.map Prod.snd) (← inferType input)
      let mut pending := remaining
      let mut seenSizes : Array Expr := #[]
      for call in found do
        if call.getAppFn.isConstOf `core.mem.size_of then
          if seenSizes.contains call then continue
          seenSizes := seenSizes.push call
        let some (calleeId, _) := targets.find? (fun target => target.2 == call.getAppFn.constName!)
          | throwError "Unknown provider-bearing native call"
        let some rowIndex := pending.findIdx? (fun row =>
            row.getObjValAs? Nat "caller_def_id" == .ok ownerId &&
            row.getObjValAs? Nat "callee_def_id" == .ok calleeId)
          | throwError "Unexpected provider-bearing native call in {ownerName}"
        let .ok rustTypes := pending[rowIndex]!.getObjValAs? (Array String) "type_arguments"
          | throwError "Provider-bearing call lacks original Rust endpoints"
        let args := call.getAppArgs
        forallTelescope (← getConstInfo call.getAppFn.constName!).type fun calleeInputs _ => do
          let (originalArgs, suffix) ← splitNativeModels calleeInputs
          let calleeParams ← typeInputs originalArgs
          unless args.size == calleeInputs.size && rustTypes.size == calleeParams.size do
            throwError "Provider-bearing call changed its original or semantic arity in {ownerName}"
          let expectedTypes ← rustTypes.mapM (originalType · params)
          for index in [:calleeParams.size] do
            let some position := originalArgs.findIdx? (· == calleeParams[index]!)
              | throwError "Native type argument is not an original input"
            unless args[position]! == expectedTypes[index]! do
              throwError "Provider-bearing call changed an original Rust endpoint in {ownerName}"
          for index in [:suffix.size] do
            let raw := (← whnf (← inferType suffix[index]!)).getAppArgs[0]!
            let some parameter := calleeParams.findIdx? (· == raw)
              | throwError "Native provider has no original type parameter"
            let canonical ← providerAt expectedTypes[parameter]! params models
            unless args[originalArgs.size + index]! == canonical do
              throwError "Provider-bearing call changed its exact retained provider in {ownerName}"
        pending := pending.extract 0 rowIndex ++ pending.extract (rowIndex + 1) pending.size
      return pending
  unless remaining.isEmpty do
    throwError "Native model providers omit original compiler call witnesses"
