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
Dictionary registration is independent of semantic laws and model selection.
This lets the canonical model resolver classify computational dictionaries
without importing law generation, which itself needs that resolver.
-/

open Lean Elab Term Meta
namespace AeneasSpecs

structure TraitLawBinding where
  raw : Name
  law : Option Name := none
  /-- Original trait type indices whose providers occur in the predicate. -/
  modelParameters : Array Nat := #[]
  deriving Inhabited

meta initialize traitLawExtension :
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

end AeneasSpecs
