/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DeriveModels
@[expose] public section
open Lean Aeneas Aeneas.Std AeneasSpecs
namespace ModelTests
set_option linter.unusedVariables false

structure Child where
  value : Nat

aeneas_model_shape Child with 0 type parameters begin
 model Positive where
   value : Nat
   positive : 0 < value
end
derive_rust_model Child with 0 type parameters decode? self =>
  if h : 0 < self.value then some ⟨self.value, h⟩ else none
check_model_binding Child with 0 type parameters

structure Parent where
  child : Child
  ignored : Nat
derive_model_shape Parent with 0 type parameters
derive_rust_model Parent with 0 type parameters
check_model_binding Parent with 0 type parameters
example : Parent.decode ⟨⟨0⟩, 1⟩ = none := rfl

structure Box (α : Type u) where
  value : Option (List α)
derive_model_shape Box with 1 type parameters
derive_rust_model Box with 1 type parameters
check_model_binding Box with 1 type parameters
example (α : Type u) [m : RustModel α] :
    (@Box.aeneasModel α m).Model = @Box.Fields α m := rfl
example (α : Type u) [m : RustModel α] :
    @Box.decode α m ⟨none⟩ = some ⟨none⟩ := rfl

inductive Choice (α : Type u) where
 | one : α → Choice α
 | empty : Choice α
derive_model_shape Choice with 1 type parameters
derive_rust_model Choice with 1 type parameters
check_model_binding Choice with 1 type parameters
example (α : Type u) [m : RustModel α] :
    @Choice.decode α m .empty = some .empty := rfl

structure SameShape where
  child : Child
  ignored : Nat
derive_model_shape SameShape with 0 type parameters
derive_rust_model SameShape with 0 type parameters
run_meta do
  if ← Lean.Meta.isDefEq (Lean.mkConst ``Parent.Fields) (Lean.mkConst ``SameShape.Fields) then
    throwError "Different owners lost nominal identity"

-- An authored Fields alias shares the one nominal carrier, including generics.
structure AliasBox (T : Type u) where
  value : T
aeneas_model_shape AliasBox with 1 type parameters begin
 model Value := Fields
end
derive_rust_model AliasBox with 1 type parameters
example (T : Type u) [m : RustModel T] : @AliasBox.Value T m = @AliasBox.Fields T m := rfl

-- Even an infallible parent that discards all children first decodes them all.
structure Forgetful where
  child : Child
aeneas_model_shape Forgetful with 0 type parameters begin
 model Value := Unit
end
derive_rust_model Forgetful with 0 type parameters decode self => ()
example : Forgetful.decode ⟨⟨0⟩⟩ = none := rfl

structure ArrayBox (T : Type u) where
  values : Aeneas.Std.Array T (2#usize)
derive_model_shape ArrayBox with 1 type parameters
derive_rust_model ArrayBox with 1 type parameters
check_model_binding ArrayBox with 1 type parameters
structure SliceBox (T : Type u) where
  values : Slice T
derive_model_shape SliceBox with 1 type parameters
derive_rust_model SliceBox with 1 type parameters
check_model_binding SliceBox with 1 type parameters

-- Nested nominal generic fields use the same original dictionary.
structure Nested (T : Type u) where
  value : Box T
derive_model_shape Nested with 1 type parameters
derive_rust_model Nested with 1 type parameters
check_model_binding Nested with 1 type parameters

structure Heterogeneous (T : Type u) where
  value : T × Nat
derive_model_shape Heterogeneous with 1 type parameters
derive_rust_model Heterogeneous with 1 type parameters

example : @RustModel.decode (Option Nat) (modelOption) none = some none := rfl
example : @RustModel.decode (core.result.Result Nat Bool) (modelRustResult) (.Err true) =
    some (.Err true) := rfl

abbrev ChildAlias := Child
example (x : ChildAlias) : @RustModel.decode ChildAlias Child.aeneasModel x = Child.decode x := rfl
example (x y : Child.Positive) (h : x.value = y.value) : x = y := Child.Positive.ext h

syntax (name := discardedModelFixture) "discard_model_fixture " command : command
@[command_elab discardedModelFixture] meta def discardModelFixture : Lean.Elab.Command.CommandElab :=
  fun stx => Lean.withoutModifyingEnv (Lean.Elab.Command.elabCommand stx[1])

structure Opaque where
  value : Nat
structure MissingParent where
  child : Opaque
/-- error: Unsupported opaque carrier or missing bound model provider: Opaque -/
#guard_msgs in
discard_model_fixture derive_model_shape MissingParent with 0 type parameters

inductive Recursive where
  | more : Recursive → Recursive
/-- error: Models require a nonrecursive, nonindexed nominal Rust type: ModelTests.Recursive -/
#guard_msgs in
discard_model_fixture derive_model_shape Recursive with 0 type parameters

inductive Indexed : Nat → Type where
  | zero : Indexed 0
/-- error: Models require a nonrecursive, nonindexed nominal Rust type: ModelTests.Indexed -/
#guard_msgs in
discard_model_fixture derive_model_shape Indexed with 0 type parameters

structure Escaping where
  continuation : Nat → Nat
/-- error: Unsupported escaping function or backward reconstruction in model carrier -/
#guard_msgs in
discard_model_fixture derive_model_shape Escaping with 0 type parameters

/-- error: A type fence must contain exactly one model shape declaration -/
#guard_msgs in
discard_model_fixture aeneas_model_shape Opaque with 0 type parameters begin
 def injection : Nat := 0
end

-- A concrete generic shape argument needs its bound dictionary. If that
-- decoder awaits ModelSupport, reject this forward dependency without fabricating
-- a temporary dictionary or silently selecting an unrelated global instance.
structure ShapeOnlyChild where
  value : Nat
derive_model_shape ShapeOnlyChild with 0 type parameters
structure ShapeOnlyBox (T : Type) where
  value : T
derive_model_shape ShapeOnlyBox with 1 type parameters
structure ForwardDictionary where
  child : ShapeOnlyBox ShapeOnlyChild
/-- error: Full model provider is not available for ModelTests.ShapeOnlyChild -/
#guard_msgs in
discard_model_fixture derive_model_shape ForwardDictionary with 0 type parameters

end ModelTests
