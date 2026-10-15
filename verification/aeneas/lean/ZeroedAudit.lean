/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import NativeModels
public meta import Lean
public section

open Lean Meta Elab

/-!
The zero-initialization primitive receives its semantic provider from the native
caller's retained model suffix. Audit the whole interpretation, the original
compiler call inventory, and each compiled application independently of its
functional proof. The pointer carrier and validator fields support dictionary
signatures only; their presence supplies no pointer execution semantics.
-/

private meta partial def zeroedCalls (expression : Expr) : Array Expr :=
  if expression.getAppFn.isConstOf `core.mem.zeroed then
    #[expression] ++ expression.getAppArgs.foldl
      (fun found arg => found ++ zeroedCalls arg) #[]
  else
    match expression with
    | .app fn arg => zeroedCalls fn ++ zeroedCalls arg
    | .lam _ ty body _ | .forallE _ ty body _ =>
      zeroedCalls ty ++ zeroedCalls body
    | .letE _ ty value body _ =>
      zeroedCalls ty ++ zeroedCalls value ++ zeroedCalls body
    | .mdata _ body | .proj _ _ body => zeroedCalls body
    | _ => #[]

private meta def checkZeroedDefinition (declName : Name)
    (expected : TSyntax `term) (binders : Array BinderInfo) : TermElabM Unit := do
  let expectedBody ← Term.elabTerm expected none
  Term.synthesizeSyntheticMVarsNoPostponing
  let expectedBody ← instantiateMVars expectedBody
  let env ← getEnv
  let some (.defnInfo actual) := env.find? declName
    | throwError "Zeroed boundary declaration {declName} must be a definition"
  unless actual.levelParams.isEmpty &&
      (← isDefEq actual.type (← inferType expectedBody)) &&
      (← isDefEq actual.value expectedBody) do
    throwError "Zeroed boundary declaration {declName} changed its full signature or body"
  forallTelescope actual.type fun inputs _ => do
    let actualBinders ← inputs.mapM fun input => do
      return (← input.fvarId!.getDecl).binderInfo
    unless actualBinders == binders do
      throwError "Zeroed boundary declaration {declName} changed its argument binders"

/-- Pin the opaque pointer data carrier and all five interface-only validators
whenever this interface boundary is present, independently of zeroed calls. -/
meta def auditInterfaceOnlyCarriers : TermElabM Unit := do
  let env ← getEnv
  let declarations := #[`Zerocopy.pointer.ptr.def.Ptr,
    `Zerocopy.Tuple.Insts.ZerocopyTryFromBytes.is_safe,
    `Zerocopy.U8.Insts.ZerocopyTryFromBytes.is_safe,
    `Zerocopy.U32.Insts.ZerocopyTryFromBytes.is_safe,
    `Zerocopy.Bool.Insts.ZerocopyTryFromBytes.is_safe,
    `Zerocopy.Array.Insts.ZerocopyTryFromBytes.is_safe]
  unless declarations.any env.contains do return
  let some (.axiomInfo carrier) := env.find? `Zerocopy.pointer.ptr.def.Ptr
    | throwError "Zeroed interfaces require the pinned opaque Ptr carrier"
  let expectedCarrier ← Term.elabType (← `(Type → Type → Type → Type → Type → Type))
  unless carrier.levelParams.isEmpty && (← isDefEq carrier.type expectedCarrier) do
    throwError "Opaque Ptr carrier changed its five-argument data-only signature"
  forallTelescope carrier.type fun inputs _ => do
    unless inputs.size == 5 do
      throwError "Opaque Ptr carrier changed its number of type arguments"
    for input in inputs do
      unless (← input.fvarId!.getDecl).binderInfo == .default do
        throwError "Opaque Ptr carrier changed its explicit type arguments"
  for (declName, raw) in #[(`Zerocopy.Tuple.Insts.ZerocopyTryFromBytes.is_safe,
        (← `(Unit))),
      (`Zerocopy.U8.Insts.ZerocopyTryFromBytes.is_safe,
        (← `(Aeneas.Std.U8))),
      (`Zerocopy.U32.Insts.ZerocopyTryFromBytes.is_safe,
        (← `(Aeneas.Std.U32))),
      (`Zerocopy.Bool.Insts.ZerocopyTryFromBytes.is_safe,
        (← `(Bool)))] do
    checkZeroedDefinition declName (← `(fun {Alignment : Type}
      (_alignment : Zerocopy.pointer.invariant.Alignment Alignment)
      (_candidate : Zerocopy.pointer.ptr.def.Ptr
        (Zerocopy.wrappers.read_only_def.ReadOnly $raw)
        (Zerocopy.pointer.invariant.Shared × Alignment ×
          Zerocopy.pointer.invariant.Initialized)
        Zerocopy.pointer.invariant.Shared Alignment
        Zerocopy.pointer.invariant.Initialized) =>
      (Aeneas.Std.Result.fail Aeneas.Std.Error.undef : Aeneas.Std.Result Bool)))
      #[.implicit, .default, .default]
  checkZeroedDefinition `Zerocopy.Array.Insts.ZerocopyTryFromBytes.is_safe
    (← `(fun {T Alignment : Type} {N : Aeneas.Std.Usize}
      (_element : Zerocopy.TryFromBytes T)
      (_alignment : Zerocopy.pointer.invariant.Alignment Alignment)
      (_candidate : Zerocopy.pointer.ptr.def.Ptr
        (Zerocopy.wrappers.read_only_def.ReadOnly (Aeneas.Std.Array T N))
        (Zerocopy.pointer.invariant.Shared × Alignment ×
          Zerocopy.pointer.invariant.Initialized)
        Zerocopy.pointer.invariant.Shared Alignment
        Zerocopy.pointer.invariant.Initialized) =>
      (Aeneas.Std.Result.fail Aeneas.Std.Error.undef : Aeneas.Std.Result Bool)))
    #[.implicit, .implicit, .implicit, .default, .default, .default]

/-- Check that every emitted native zeroed call retains the exact original type
variable and that variable's exact model provider. Compiler call rows retain
ownership and multiplicity across lowering; split-loop bodies consume the same
owner's aggregate inventory. Only the currently extracted T0 endpoint is
supported, so adding another endpoint requires an explicit audit extension. -/
meta def auditZeroed (bindings : Json) : TermElabM Unit := do
  auditInterfaceOnlyCarriers
  unless (← getEnv).contains `core.mem.zeroed do return
  checkZeroedDefinition `core.mem.zeroed
    (← `(fun (T : Type) [model : AeneasSpecs.RustModel T] => model.zeroedResult))
    #[.default, .instImplicit]
  let .ok admission := bindings.getObjVal? "admission"
    | throwError "Zeroed requires original compiler admission"
  let .ok stages := admission.getObjVal? "stages"
    | throwError "Zeroed requires both compiler admission stages"
  let .ok original := stages.getObjVal? "before"
    | throwError "Zeroed lacks original compiler admission"
  let .ok lowered := stages.getObjVal? "llbc"
    | throwError "Zeroed lacks lowered compiler admission"
  let .ok originalCalls := original.getObjValAs? (Array Json) "calls"
    | throwError "Zeroed lacks original compiler call evidence"
  let .ok loweredCalls := lowered.getObjValAs? (Array Json) "calls"
    | throwError "Zeroed lacks lowered compiler call evidence"
  let originalZeroed := originalCalls.filter fun row =>
    row.getObjValAs? String "callee" == .ok "core::mem::zeroed"
  let loweredZeroed := loweredCalls.filter fun row =>
    row.getObjValAs? String "callee" == .ok "core::mem::zeroed"
  unless originalZeroed == loweredZeroed do
    throwError "Zeroed changed original Rust type arguments, ownership, or multiplicity"
  let .ok executions := lowered.getObjValAs? (Array Json) "executions"
    | throwError "Zeroed lacks the complete admitted execution closure"
  for row in loweredZeroed do
    let .ok rust := row.getObjValAs? String "caller"
      | throwError "Zeroed compiler call lacks its Rust owner"
    let .ok _ := row.getObjValAs? Nat "caller_def_id"
      | throwError "Zeroed compiler call lacks its original compiler identity"
    unless row.getObjValAs? (Array String) "type_arguments" == .ok #["T0"] do
      throwError "Unsupported original Rust zeroed endpoint in {rust}"
    unless executions.any (fun execution =>
        execution.getObjValAs? String "rust" == .ok rust &&
        execution.getObjValAs? String "origin" == .ok "body") do
      throwError "Zeroed call owner {rust} is not an admitted native body"
  let nativeText ← IO.FS.readFile "Zerocopy/translation.json"
  let .ok native := Json.parse nativeText
    | throwError "Invalid native zeroed call map"
  let .ok functions := native.getObjValAs? (Array Json) "functions"
    | throwError "Missing native zeroed function inventory"
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut remaining := loweredZeroed
  -- Native dictionaries can spell a Rust owner differently from admission.
  -- Inspect every emitted body and match calls by their compiler identities,
  -- rather than skipping helpers whose displayed owner names differ.
  for candidate in functions do
    let .ok isOpaque := candidate.getObjValAs? Bool "is_opaque"
      | throwError "Native zeroed owner lacks its body disposition"
    if isOpaque then continue
    let .ok ident := candidate.getObjValAs? Nat "def_id"
      | throwError "Native zeroed owner lacks its compiler identity"
    let .ok raw := candidate.getObjValAs? String "lean_name"
      | throwError "Native zeroed owner lacks its compiled name"
    unless !names.contains raw.toName do
      throwError "Repeated native zeroed owner {raw}"
    names := names.push raw.toName
    let some (.defnInfo owner) := env.find? raw.toName
      | throwError "Native zeroed owner {raw} must retain its compiled body"
    remaining ← lambdaTelescope owner.value fun inputs body => do
      let mut calls := zeroedCalls body
      for input in inputs do
        calls := calls ++ zeroedCalls (← inferType input)
      if calls.isEmpty then return remaining
      let (original, models) ← AeneasSpecs.splitNativeModels inputs
      let typeInputs ← original.filterM fun input => do
        match ← whnf (← inferType input) with
        | .sort level => return !level.isZero
        | _ => return false
      let some target := typeInputs[0]?
        | throwError "Native zeroed owner {raw} lacks original Rust type variable T0"
      let matchingModels ← models.filterM fun model => do
        let type ← whnf (← inferType model)
        return type.getAppFn.isConstOf ``AeneasSpecs.RustModel &&
          type.getAppArgs == #[target]
      unless matchingModels.size == 1 do
        throwError "Native zeroed owner {raw} lacks the exact retained T0 provider"
      let mut unconsumed := remaining
      for call in calls do
        let args := call.getAppArgs
        unless args.size == 2 && args[0]! == target &&
            args[1]! == matchingModels[0]! do
          throwError "Native zeroed call in {raw} changed its original type or retained provider"
        let some index := unconsumed.findIdx? (fun row =>
            row.getObjValAs? Nat "caller_def_id" == .ok ident)
          | throwError "Unexpected compiled zeroed call in {raw}"
        unconsumed := unconsumed.extract 0 index ++
          unconsumed.extract (index + 1) unconsumed.size
      return unconsumed
  unless remaining.isEmpty do
    throwError "Compiled zeroed calls omit original compiler call witnesses"
