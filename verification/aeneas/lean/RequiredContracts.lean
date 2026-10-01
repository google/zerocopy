/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import SpecsSyntax
public import ContractSimps
public import Mathlib.Tactic.Convert
public section

/-!
A proved specification can still state too little. For example, a postcondition
`True` can be proved for identity but also permits identity to return the wrong
value. This module checks adequacy by replacing the actual execution with an
arbitrary `Result` and proving that the authored contract implies a separately
authored expectation for that same outcome.

Only after that implication is checked do we specialize it to the extracted
call and apply the canonical proof. The audits require the expected family to
use its outcome and forbid dependencies on the extracted operation, including
through helper declarations. Its concrete alias must also specialize that same
family. These checks prevent an adapter from bypassing the authored contract by
independently proving the implementation again.
-/

open Lean Lean.Meta Aeneas Aeneas.Std

namespace AeneasContracts

attribute [contract_simps] WP.spec_equiv_exists UScalar.eq_equiv
  UScalar.coe_max UScalar.lt_equiv UScalar.le_equiv

/-- A required check starts from a canonical proof of a named specification.
Accepting arbitrary terms here would let a check ignore the inline contract. -/
meta def canonicalSpecName (candidate : Name) : MetaM Name := do
  let .thmInfo proof ← getConstInfo candidate
    | throwError "Required contract candidate must be a theorem: {candidate}"
  let .const specName _ := proof.type.consumeMData
    | throwError "Required contract candidate must directly name a specification: {candidate}"
  unless AeneasSpecs.specAttribute.hasTag (← getEnv) specName do
    throwError "Required contract candidate must directly name a specification: {candidate}"
  pure specName

/-- An independent family must describe the supplied outcome, rather than
smuggling the concrete call back into the expectation through a helper. -/
private meta def checkIndependentFamily (familyName modelName : Name)
    (count : Nat) : MetaM Unit := do
  let info ← getConstInfo familyName
  let some value := info.value? | throwError "Independent contract must be transparent: {familyName}"
  -- Open the function type to get the actual input/outcome variables, then
  -- reduce its body enough to reject a syntactically present but ignored run.
  forallTelescope info.type fun inputs _ => do
    unless inputs.size == count + 1 do
      throwError "Independent contract {familyName} changed its input and outcome prefix"
    let body ← whnf (mkAppN value inputs)
    unless body.containsFVar inputs[count]!.fvarId! do
      throwError "Independent contract {familyName} must use its execution outcome"
  -- Walk types as well as bodies. An opaque helper can mention the extracted
  -- operation only in its type; inspecting reduced bodies would miss that
  -- dependency and admit a family with an implementation-specific premise.
  let mut pending := info.type.getUsedConstants ++ value.getUsedConstants
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if current == modelName then
      throwError "Independent contract {familyName} depends on its extracted operation"
    if seen.contains current then continue
    seen := seen.insert current
    let dependency ← getConstInfo current
    pending := pending ++ dependency.type.getUsedConstants
    if let some body := dependency.value? (allowOpaque := true) then
      pending := pending ++ body.getUsedConstants

/-- Compare the contract for every possible execution outcome. The independent
family must also specialize to its independently authored concrete proposition.
No extracted function body is available as a premise of this implication. -/
meta def contractAdequacyType (specName expectedName : Name) : MetaM Expr := do
  AeneasSpecs.checkSpecContract specName
  let (modelName, count) ← AeneasSpecs.specBinding specName
  checkIndependentFamily (expectedName.appendAfter "_contract") modelName count
  let family ← mkConstWithFreshMVarLevels (AeneasSpecs.specContractName specName)
  forallTelescope (← inferType family) fun inputs resultType => do
    unless inputs.size == count + 1 && resultType.consumeMData == mkSort .zero do
      throwError "Required comparison has an unexpected contract family type"
    let expectedAt ← mkAppM (expectedName.appendAfter "_contract") inputs
    let expectedFamily := expectedAt.getAppFn
    unless ← isDefEq (← inferType expectedAt) (mkSort .zero) do
      throwError "Independent contract family must have the same input and outcome types"
    -- Quantify over arbitrary run, then form AuthoredAt -> RequiredAt. The
    -- actual extracted call is introduced only in the specialization check
    -- below, so it cannot prove away a weak post or an accidentally empty domain.
    let implication ← mkArrow (mkAppN family inputs) expectedAt
    let adequacy ← mkForallFVars inputs implication
    -- The concrete expectation and its family must be two views of the same
    -- promise. Otherwise a true alias could conceal a false expected family.
    let .defnInfo source ← getConstInfo specName
      | throwError "Expected a transparent specification"
    forallTelescope (source.value.instantiateLevelParams source.levelParams family.constLevels!) fun sourceInputs body => do
      let call := body.consumeMData.getAppArgs[1]!
      let originalInputs := sourceInputs.extract 0 count
      let concrete := mkAppN expectedFamily (originalInputs.push call)
      let specialized ← mkForallFVars originalInputs concrete
      unless ← isDefEq (← mkConstWithFreshMVarLevels expectedName) specialized do
        throwError "Independent proposition {expectedName} does not specialize its arbitrary-outcome family"
    instantiateMVars adequacy

elab "contract_adequacy% " source:ident " implies " expected:ident : term => do
  let specName ← Elab.realizeGlobalConstNoOverloadWithInfo source
  let expectedName ← Elab.realizeGlobalConstNoOverloadWithInfo expected
  contractAdequacyType specName expectedName

-- Only after adequacy is proved may its abstract outcome be specialized to
-- the actual call and supplied canonical proof.
elab "required_contract_instance% " candidate:ident " with " adequate:ident : term => do
  let proofName ← Elab.realizeGlobalConstNoOverloadWithInfo candidate
  let adequateName ← Elab.realizeGlobalConstNoOverloadWithInfo adequate
  let specName ← canonicalSpecName proofName
  let (modelName, count) ← AeneasSpecs.specBinding specName
  let family ← mkConstWithFreshMVarLevels (AeneasSpecs.specContractName specName)
  forallTelescope (← inferType family) fun inputs _ => do
    let originals := inputs.extract 0 count
    -- The audited prefix includes implicit Rust type arguments. Apply it
    -- literally; mkAppM would instead insert them and treat the first supplied
    -- type as a value argument for an implicit-generic extracted operation.
    let call ← mkAppOptM modelName (originals.map some)
    let proof ← mkAppOptM proofName (originals.map some)
    let value ← mkAppOptM adequateName ((originals ++ #[call, proof]).map some)
    let _ ← inferType value
    mkLambdaFVars originals (← instantiateMVars value)

/-- Generate a kernel-checked implication about arbitrary outcomes, then apply
it to the proved implementation. Normalization can use a domain-specific lemma,
but it cannot substitute a second proof of the concrete implementation. -/
elab "check_contract " expected:ident " using " candidate:term : command => do
  let candidateId ← match candidate with
    | `(@$id:ident) => pure id
    | `($id:ident) => pure id
    | _ => throwErrorAt candidate "Required contract candidate must be a bare canonical theorem"
  let (specName, count, dictionaryCount) ← Elab.Command.liftTermElabM do
    let proofName ← Elab.realizeGlobalConstNoOverloadWithInfo candidateId
    let specName ← canonicalSpecName proofName
    let (_, count) ← AeneasSpecs.specBinding specName
    let .defnInfo source ← getConstInfo specName
      | throwError "Expected a transparent specification"
    let dictionaryCount ← forallTelescope source.value fun inputs _ => do
      let mut dictionaries := 0
      for input in inputs[:count] do
        if (← whnf (← inferType input)).isSort then
          dictionaries := dictionaries + 1
      pure dictionaries
    pure (specName, count, dictionaryCount)
  let source := mkIdentFrom candidateId specName
  let family := mkIdentFrom expected (expected.getId.appendAfter "_contract")
  let sourceFamily := mkIdentFrom candidateId (AeneasSpecs.specContractName specName)
  let adequate := mkIdentFrom expected (expected.getId.appendAfter "_adequate")
  let witness := mkIdentFrom expected (expected.getId.appendAfter "_checked")
  let arguments := (List.range (count + 1)).toArray.map
    (fun i => mkIdent (Name.mkSimple s!"_contractInput{i}"))
  let dictionaries := (List.range dictionaryCount).toArray.map
    (fun i => mkIdent (Name.mkSimple s!"_contractDictionary{i}"))
  -- Source type parameters contribute original model dictionaries after run.
  -- Specialize the authored premise with those same dictionaries before proving
  -- the independent implication; ghost instances cannot select new meanings.
  let introduceDictionaries ← if dictionaries.isEmpty then `(tactic| skip) else
    `(tactic| (intro $dictionaries:ident*; specialize @provided $dictionaries:ident*))
  -- These tactics produce an ordinary theorem, not a trusted comparison
  -- result. They normalize known decoder/word facts and align forall/exists
  -- witnesses. If the implication is false or needs a new lemma, elaboration
  -- fails rather than falling back to a proof of the concrete operation.
  Elab.Command.elabCommand (← `(theorem $adequate :
      contract_adequacy% $source implies $expected := by
    intro $arguments:ident* provided
    $introduceDictionaries:tactic
    first
    | exact provided
    | (simp (disch := assumption) only [contract_simps]; done)
    | try unfold $family
      try unfold $sourceFamily at provided
      convert provided using 1 <;>
        (simp only [WP.spec_equiv_exists]
         all_goals simp (config := { index := false, contextual := true }) only [contract_simps])
      all_goals
        (congr! 2
         all_goals first | rfl | (split <;> simp_all only [contract_simps]) | skip)
      all_goals
        (congr! 4
         all_goals first | rfl | (split <;> simp_all only [contract_simps]) | grind)
      all_goals rfl))
  if ← MonadLog.hasErrors then return
  Elab.Command.elabCommand (← `(theorem $witness : $expected :=
    required_contract_instance% $candidateId with $adequate))

end AeneasContracts
