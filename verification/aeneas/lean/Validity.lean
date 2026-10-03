/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public meta import Lean
@[expose] public section

open Lean Lean.Meta Aeneas.Std
namespace AeneasSpecs

/-- A conditional contract's representation predicate, not a claim about every
Rust inhabitant. Generic specifications quantify over this dictionary. -/
class IsValid (α : Type u) where
  isValid : α → Prop

private meta initialize canonicalExtension :
    SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun names provider => if names.contains provider then names else names.push provider
    addImportedFn := fun entries => entries.foldl (fun names providers =>
      providers.foldl (fun names provider => if names.contains provider then names else names.push provider) names) #[]
  }

meta def registerCanonicalValidity (provider : Name) : MetaM Unit :=
  modifyEnv (canonicalExtension.addEntry · provider)

-- Primitive/container providers are discovered from the class-defining module's
-- ordinary instance metadata. Native and derived providers add generated tags.
meta def canonicalValidityProviders : MetaM (Array Name) := do
  let env ← getEnv
  let mut providers := canonicalExtension.getState env
  if let some moduleIndex := env.getModuleIdxFor? ``IsValid then
    for entry in Meta.instanceExtension.ext.getModuleEntries env moduleIndex do
      let .global instanceEntry := entry | continue
      let some provider := instanceEntry.globalName? | continue
      let info ← getConstInfo provider
      let canonical ← Meta.forallTelescope info.type fun _ target =>
        pure (target.isAppOfArity ``IsValid 1)
      if canonical && !providers.contains provider then providers := providers.push provider
  return providers

meta initialize canonicalValidityAttribute : TagAttribute ←
  registerTagAttribute `validity_canonical
    "A fixed representation-validity dictionary checked before specification ghosts"
    (validate := fun provider => modifyEnv (canonicalExtension.addEntry · provider))

/-- Borrow reconstruction functions are not representation-validity values.
Check nested container arguments as well as an immediately function-valued carrier. -/
meta partial def rejectEscapingFunctions (carrierType : Expr) : Meta.MetaM Unit := do
  let carrierType ← Meta.whnf carrierType
  if carrierType.isForall then
    throwError "Unsupported escaping function or backward reconstruction in validity carrier"
  for arg in carrierType.getAppArgs do
    if (← Meta.whnf (← Meta.inferType arg)).isSort then
      rejectEscapingFunctions arg

abbrev isValid {α : Type u} [IsValid α] (x : α) : Prop := IsValid.isValid x

instance validUScalar : IsValid (UScalar ty) := ⟨fun _ => True⟩
instance validIScalar : IsValid (IScalar ty) := ⟨fun _ => True⟩
instance validBool : IsValid Bool := ⟨fun _ => True⟩
instance validNat : IsValid Nat := ⟨fun _ => True⟩
instance validInt : IsValid Int := ⟨fun _ => True⟩
instance validUnit : IsValid Unit := ⟨fun _ => True⟩

instance validProd [IsValid α] [IsValid β] : IsValid (α × β) :=
  ⟨fun x => isValid x.1 ∧ isValid x.2⟩
instance validOption [IsValid α] : IsValid (Option α) :=
  ⟨fun xs => ∀ x ∈ xs, isValid x⟩
instance validList [IsValid α] : IsValid (List α) :=
  ⟨fun xs => ∀ x ∈ xs, isValid x⟩
instance validSlice [IsValid α] : IsValid (Slice α) :=
  ⟨fun xs => isValid xs.val⟩
instance validArray [IsValid α] : IsValid (Aeneas.Std.Array α n) :=
  ⟨fun xs => isValid xs.val⟩
instance validRustResult [IsValid α] [IsValid β] :
    IsValid (core.result.Result α β) :=
  ⟨fun x => match x with | .Ok x => isValid x | .Err e => isValid e⟩

end AeneasSpecs
