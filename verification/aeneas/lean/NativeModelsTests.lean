/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import NativeModels
@[expose] public section
open AeneasSpecs Aeneas.Std Aeneas.Std.Result Lean Meta Elab Command
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

namespace NativeModelsTests

def modeledLeaf (T : Type) [RustModel T] : Result T := .fail .undef
structure ComputationalDict (T : Type) where run : T → Nat

@[reducible]
native_models def independent (T : Type) {U : Type} (unused : Nat)
    (dict : ComputationalDict T) : Nat := 7
native_models def dependent (T : Type) {U : Type} (unused : Nat)
    (dict : ComputationalDict T) : Result T := modeledLeaf T
native_models def interleaved (unused : Nat) (T U : Type)
    (dict : ComputationalDict U) : Result U := modeledLeaf U
native_models def both (T U : Type) (unused : Nat) : Result (T × U) := do
  let t ← modeledLeaf T
  let u ← modeledLeaf U
  ok (t, u)
native_models def higher {T : Type} (dict : {V : Type} → V → V)
    (unused : Nat) : Nat := 8
native_models def instanceArgument (T : Type) [inh : Inhabited T]
    (unused : Nat) : T := default
native_models def typeReturn (T U : Type) (unused : Nat) : Type := T
native_models def untypedReturn (T : Type) (unused : Nat) := 3
native_models def noArguments : Nat := 4

-- A dependent do-body used to elaborate under the beta wrapper's fresh type.
-- The anonymous lets must retain Self without changing the expected Result Self.
@[trait_default]
native_models def defaultDo (Self : Type) : Result Self := do
  modeledLeaf Self
example (Self : Type) [m : RustModel Self] :
    @defaultDo Self m = @modeledLeaf Self m := rfl
native_models def typedResult (T : Type) (x : T) : Option (ModelOf T) :=
  RustModel.decode x
native_models def containerResult (T : Type) (xs : List T) : Option (ModelOf (List T)) :=
  RustModel.decode xs
native_models def laterIndependent (T : Type) (unused : Nat) : Nat := 9
native_models def preservesUndef (T : Type) (unused : Nat) : Result T := .fail .undef
native_models def providerCollision (T : Type) (_nativeModel0 : Nat) : Result T := modeledLeaf T

example (T U : Type) (n : Nat) (dict : ComputationalDict T) :
    @independent T U n dict = 7 := rfl
example (T U : Type) (n : Nat) (dict : ComputationalDict T) [m : RustModel T] :
    @dependent T U n dict m = @modeledLeaf T m := rfl
example (T U : Type) (n : Nat) (dict : ComputationalDict U) [m : RustModel U] :
    @interleaved n T U dict m = @modeledLeaf U m := rfl
example (T U : Type) (n : Nat) [mt : RustModel T] [mu : RustModel U] :
    @both T U n mt mu = (do let t ← @modeledLeaf T mt; let u ← @modeledLeaf U mu; ok (t, u)) := rfl
example (T : Type) (dict : {V : Type} → V → V) (n : Nat) :
    @higher T dict n = 8 := rfl
example (T : Type) [i : Inhabited T] (n : Nat) :
    @instanceArgument T i n = i.default := rfl
example (T U : Type) (n : Nat) : typeReturn T U n = T := rfl
example (T : Type) (x : T) [m : RustModel T] :
    @typedResult T x m = m.decode x := rfl
example (T : Type) (xs : List T) [m : RustModel T] :
    @containerResult T xs m = (@modelList T m).decode xs := rfl
example (T : Type) (n : Nat) : @preservesUndef T n = .fail .undef := rfl
example (T : Type) (n : Nat) [m : RustModel T] :
    @providerCollision T n m = @modeledLeaf T m := rfl

run_meta do
  for (decl, expectedNames, suffixCount) in #[
      (``independent, #[`T, `U, `unused, `dict], 0),
      (``dependent, #[`T, `U, `unused, `dict], 1),
      (``defaultDo, #[`Self], 1),
      (``noArguments, #[], 0),
      (``untypedReturn, #[`T, `unused], 0),
      (``interleaved, #[`unused, `T, `U, `dict], 1),
      (``both, #[`T, `U, `unused], 2),
      (``higher, #[`T, `dict, `unused], 0),
      (``instanceArgument, #[`T, `inh, `unused], 0),
      (``typeReturn, #[`T, `U, `unused], 0),
      (``preservesUndef, #[`T, `unused], 0),
      (``typedResult, #[`T, `x], 1),
      (``containerResult, #[`T, `xs], 1),
      (``laterIndependent, #[`T, `unused], 0),
      (``providerCollision, #[`T, `_nativeModel0], 1)] do
    forallTelescope (← inferType (mkConst decl)) fun args _ => do
      let (original, models) ← splitNativeModels args
      unless original.size == expectedNames.size && models.size == suffixCount do
        throwError "Wrong native model argument counts for {decl}"
      for arg in original, expected in expectedNames do
        unless (← arg.fvarId!.getDecl).userName == expected do
          throwError "Wrong native argument order for {decl}"


-- Ordinary explicit headers keep these deliberately malformed suffixes intact.
def badMiddle (T : Type) [m : RustModel T] (n : Nat) : Nat := n
def badExplicit (T : Type) (m : RustModel T) : Nat := 0
def badOrder (T U : Type) [mu : RustModel U] [mt : RustModel T] : Nat := 0
def badDuplicate (T : Type) [m1 : RustModel T] [m2 : RustModel T] : Nat := 0
def badContainer (T : Type) [m : RustModel (List T)] : Nat := 0
def badConcrete [m : RustModel Nat] : Nat := 0

run_meta do
  for decl in #[``badMiddle, ``badExplicit, ``badOrder, ``badDuplicate,
      ``badContainer, ``badConcrete] do
    forallTelescope (← inferType (mkConst decl)) fun args _ => do
      let rejected ← try
        let _ ← splitNativeModels args
        pure false
      catch _ => pure true
      unless rejected do throwError "Expected malformed model suffix rejection: {decl}"
  let rejected ← try
    let _ ← splitNativeModels #[mkConst ``Nat]
    pure false
  catch _ => pure true
  unless rejected do throwError "Expected non-variable rejection"

/-- error: native_models requires typed binders without defaults -/
#guard_msgs in
native_models def rejectsDefault (x : Nat := 2) : Nat := x

/-- error: native_models does not support anonymous arguments -/
#guard_msgs in
native_models def rejectsAnonymous (_ : Nat) : Nat := 0

/-- error: native_models does not support declaration-local universes -/
#guard_msgs in
native_models def rejectsUniverse.{u} (T : Type u) : Type u := T

/-- error: native_models requires a plain := body -/
#guard_msgs in
native_models def rejectsEquations : Nat → Nat
  | n => n

/-- error: native_models requires distinct argument names -/
#guard_msgs in
native_models def rejectsShadow (T : Type) (T : Type) : Type := T

/-- error: native_models requires a plain := body -/
#guard_msgs in
native_models def rejectsWhere (x : Nat) : Nat := aux x
where aux (x : Nat) := x

end NativeModelsTests
