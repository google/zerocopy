/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Specs
open Lean Elab Command Meta AeneasSpecs Aeneas.Std

/-!
`inspect_spec` explains a compiled specification: its original raw call,
selected providers, decoded input premises, result admission, and postconditions.
It reads the elaborated Lean expressions used by the checker. It does not
reconstruct a contract from annotation text or run a new verification build.
The shape checks below keep the report tied to the generated decoded-result
form, so inspection fails if that form no longer supports the reported meaning.
-/


private meta def inspectionExpr (e : Expr) : MetaM Format :=
  withOptions (fun o => o.setBool `pp.proofs true) (ppExpr e)

/-- Inspect compiled expressions, keeping the same original-call audit as Check.
No syntax expansion or independent specification interpretation is involved. -/
elab "inspect_spec " candidate:ident : command => liftTermElabM do
  let specName ← Elab.realizeGlobalConstNoOverloadWithInfo candidate
  let (modelName, originalCount) ← specBinding specName
  let info ← getConstInfo specName
  let some proposition := info.value? | throwError "Missing specification value {specName}"
  logInfo m!"Elaborated proposition {specName}:\n{← inspectionExpr proposition}"
  forallTelescope proposition fun inputs body => do
    let args := body.consumeMData.getAppArgs
    let call := args[1]!
    logInfo m!"Original target: {modelName}\nOriginal raw call: {← withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.fullNames true) (inspectionExpr call)}"
    let mode := if body.consumeMData.getAppFn.isConstOf ``WP.spec then "total (WP.spec)"
      else "partial (WP.dspec)"
    logInfo m!"Execution: {mode}"
    for i in [:inputs.size] do
      let input := inputs[i]!
      let decl ← input.fvarId!.getDecl
      let ty := decl.type.consumeMData
      -- Binder position identifies original raw/type arguments. Later shapes
      -- are classified for reporting only; this is not a second domain checker.
      if i < originalCount then
        logInfo m!"Original binder {decl.userName}: {← inspectionExpr ty}"
      else if ty.isAppOfArity ``RustModel 1 then
        logInfo m!"Provider binder (original dictionary or ghost) {decl.userName}: {← inspectionExpr ty}"
      else if ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``RustModel.decode 3 then
        let decoding := ty.getAppArgs[1]!.getAppArgs
        logInfo m!"Input domain {decl.userName}: {← inspectionExpr ty}\nSelected provider: {← withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.fullNames true) (inspectionExpr decoding[1]!)}"
      else if ← isProp ty then
        logInfo m!"Premise or proposition-valued ghost {decl.userName}: {← inspectionExpr ty}"
      else
        logInfo m!"Mathematical witness or ghost {decl.userName}: {← inspectionExpr ty}"
    let post := args[2]!
    -- Unpack exactly one raw output, one existential model witness, and its
    -- decoder equation. Check variable identities so a report cannot call a
    -- different result's decoding the admission condition for this return.
    lambdaTelescope post fun resultInputs resultBody => do
      unless resultInputs.size == 1 && resultBody.isAppOfArity ``Exists 2 do
        throwError "Specification {specName} lacks the expected decoded-result existential"
      lambdaTelescope resultBody.getAppArgs[1]! fun witnesses conjunction => do
        unless witnesses.size == 1 && conjunction.isAppOfArity ``And 2 do
          throwError "Specification {specName} lacks the expected result decoding conjunction"
        let equation := conjunction.getAppArgs[0]!
        unless equation.isAppOfArity ``Eq 3 &&
            equation.getAppArgs[1]!.isAppOfArity ``RustModel.decode 3 do
          throwError "Specification {specName} lacks an explicit result decoder equation"
        let decoding := equation.getAppArgs[1]!.getAppArgs
        let accepted := equation.getAppArgs[2]!
        unless decoding[2]!.consumeMData == resultInputs[0]! &&
            accepted.isAppOfArity ``Option.some 2 &&
            accepted.getAppArgs[1]!.consumeMData == witnesses[0]! do
          throwError "Specification {specName} does not require successful decoding of its original result"
        logInfo m!"Result domain: {← inspectionExpr (← inferType witnesses[0]!)}\nSelected result provider: {← withOptions (fun o => (o.setBool `pp.explicit true).setBool `pp.fullNames true) (inspectionExpr decoding[1]!)}\nRequired result decoding: {← inspectionExpr equation}\nPostconditions: {← inspectionExpr conjunction.getAppArgs[1]!}"
  let axioms ← collectAxioms specName
  logInfo m!"Compiled axiom dependencies: {axioms}"
