/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DeriveModels
@[expose] public section

/-!
These fixtures challenge structural model generation independently of zerocopy's
layout models. They cover generic shapes and dictionaries, nominal identity,
containers, enum payloads, and lossy local decoders. The rejected-child cases
are essential: an infallible parent that forgets a field must still reject that
field's invalid raw representation. Decomposition checks also pin the accepted
witness order rather than merely checking one decoder result.
-/

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
    (@Box.aeneasModel α m).Model = Box.Fields m.Model := rfl
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

-- Even unused Rust generics retain their dictionary and carrier parameter.
structure Phantom (T : Type u) where
  value : Nat
aeneas_model_shape Phantom with 1 type parameters begin
 model Value := Unit
end
derive_rust_model Phantom with 1 type parameters decode self => ()
check_model_binding Phantom with 1 type parameters
example (T : Type u) [m : RustModel T] :
    @Phantom.decode T m ⟨7⟩ = some () := rfl

-- An authored Fields alias shares the one nominal carrier, including generics.
structure AliasBox (T : Type u) where
  value : T
aeneas_model_shape AliasBox with 1 type parameters begin
 model Value := Fields
end
derive_rust_model AliasBox with 1 type parameters
example (T : Type u) [m : RustModel T] : AliasBox.Value m.Model = AliasBox.Fields m.Model := rfl

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

-- Concrete generic shape arguments require only their mathematical shape.
-- The child decoder deliberately appears after the containing shape.
structure RoundingRaw where
  word : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner
aeneas_model_shape RoundingRaw with 0 type parameters begin
 model RoundingValue where
   value : Nat
   positive : 0 < value
end
structure Wrapper (T : Type u) where
  value : T
derive_model_shape Wrapper with 1 type parameters
structure BeforeDecoder where
  child : Wrapper RoundingRaw
  choices : Option (List (Wrapper RoundingRaw))
  slice : Slice (Wrapper RoundingRaw)
  array : Aeneas.Std.Array (Wrapper RoundingRaw) (2#usize)
derive_model_shape BeforeDecoder with 0 type parameters
example : BeforeDecoder.Fields → Wrapper.Fields RoundingRaw.RoundingValue := fun x => x.child
example : BeforeDecoder.Fields → SliceValue (Wrapper.Fields RoundingRaw.RoundingValue) :=
  fun x => x.slice
example : BeforeDecoder.Fields → ArrayValue (Wrapper.Fields RoundingRaw.RoundingValue) (2#usize) :=
  fun x => x.array

derive_rust_model RoundingRaw with 0 type parameters decode self =>
  ⟨self.word.value, self.word.positive⟩
derive_rust_model Wrapper with 1 type parameters
derive_rust_model BeforeDecoder with 0 type parameters
check_model_binding BeforeDecoder with 0 type parameters

-- Later dictionaries retain distinct meanings despite sharing one shape family.
@[reducible] def identityDictionary : RustModel Nat := ⟨Nat, some⟩
@[reducible] def doubleDictionary : RustModel Nat := ⟨Nat, fun n => some (2 * n)⟩
example : @Wrapper.decode Nat identityDictionary ⟨13⟩ = some ⟨13⟩ := rfl
example : @Wrapper.decode Nat doubleDictionary ⟨13⟩ = some ⟨26⟩ := rfl
example : (@Wrapper.aeneasModel Nat identityDictionary).Model =
    (@Wrapper.aeneasModel Nat doubleDictionary).Model := rfl

-- Authored generic shapes bind TModel; decoding still has the actual T dictionary.
structure Authored (T : Type u) where
  value : T
aeneas_model_shape Authored with 1 type parameters begin
 model Value where
   value : TModel
end
derive_rust_model Authored with 1 type parameters decode self =>
  { value := (self.value : ModelOf T) }
check_model_binding Authored with 1 type parameters
example (TModel : Type u) : Authored.Value TModel → TModel := fun x => x.value

-- An infallible lossy parent still rejects a malformed native nonzero child.
structure ForgetfulWord where
  word : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner
aeneas_model_shape ForgetfulWord with 0 type parameters begin
 model Value := Unit
end
derive_rust_model ForgetfulWord with 0 type parameters decode self => ()
example : ForgetfulWord.decode ⟨⟨0#usize⟩⟩ = none := rfl
example (raw : ForgetfulWord) : ForgetfulWord.decode raw = some () ↔
    ∃ word, (modelNonZeroUsize).decode raw.word = some word ∧
      ForgetfulWord.decodeFields ⟨word⟩ = some () := ForgetfulWord.decode_decompose raw ()

-- Separate universe parameters and container bounds remain present.
structure Mixed (A : Type u) (B : Type v) where
  value : A × Option B
derive_model_shape Mixed with 2 type parameters
derive_rust_model Mixed with 2 type parameters
check_model_binding Mixed with 2 type parameters
example (A : Type u) (B : Type v) : Mixed.Fields A B → A × Option B := fun x => x.value
example (T : Type u) [m : RustModel T] (x : ArrayBox.Fields m.Model) :
    x.values.val.length = (2#usize).val := x.values.property
example (T : Type u) [m : RustModel T] (x : SliceBox.Fields m.Model) :
    x.values.val.length ≤ Usize.max := x.values.property

-- Decomposition exposes every child's decoded witness, including forgotten data.
example (raw : Forgetful) : Forgetful.decode raw = some () ↔
    ∃ child, Child.decode raw.child = some child ∧
      Forgetful.decodeFields ⟨child⟩ = some () := Forgetful.decode_decompose raw ()
example (raw : Parent) (value : Parent.Fields) : Parent.decode raw = some value ↔
    ∃ child, Child.decode raw.child = some child ∧
      ∃ ignored, (modelNat).decode raw.ignored = some ignored ∧
        Parent.decodeFields ⟨child, ignored⟩ = some value := Parent.decode_decompose raw value
example (T : Type u) [m : RustModel T] (x : T) (value : Choice.Fields m.Model) :
    @Choice.decode T m (.one x) = some value ↔
      ∃ child, m.decode x = some child ∧ @Choice.decodeFields T m (.one child) = some value :=
  Choice.decode_decompose T (.one x) value
example (T : Type u) [m : RustModel T] (value : Choice.Fields m.Model) :
    @Choice.decode T m .empty = some value ↔ @Choice.decodeFields T m .empty = some value :=
  Choice.decode_decompose T .empty value

-- An enum traverses exactly its selected payload. The local decoder forgets
-- both fields, but the second field's rejection must still reject the pair.
-- Its empty case has no child admission obligation.
inductive ForgetfulChoice where
 | pair : Nat → Child → ForgetfulChoice
 | empty : ForgetfulChoice
aeneas_model_shape ForgetfulChoice with 0 type parameters begin
 model Value := Unit
end
derive_rust_model ForgetfulChoice with 0 type parameters decode self => ()
check_model_binding ForgetfulChoice with 0 type parameters
example : ForgetfulChoice.decode (.pair 7 ⟨0⟩) = none := rfl
example : ForgetfulChoice.decode (.pair 7 ⟨1⟩) = some () := rfl
example : ForgetfulChoice.decode .empty = some () := rfl
example (n : Nat) (raw : Child) : ForgetfulChoice.decode (.pair n raw) = some () ↔
    ∃ number, modelNat.decode n = some number ∧
      ∃ child, Child.decode raw = some child ∧
        ForgetfulChoice.decodeFields (.pair number child) = some () :=
  ForgetfulChoice.decode_decompose (.pair n raw) ()
example : ForgetfulChoice.decode .empty = some () ↔
    ForgetfulChoice.decodeFields .empty = some () :=
  ForgetfulChoice.decode_decompose .empty ()

-- Audit the generated bridge terms as well as their successful elaboration.
run_meta do
  for owner in ← modelOwnerNames do
    if !(`ModelTests).isPrefixOf owner then continue
    let theoremName := owner ++ `decode_decompose
    let .thmInfo _ ← getConstInfo theoremName
      | throwError "Missing structural decomposition theorem for {owner}"
    for axiomName in ← Lean.collectAxioms theoremName do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Unexpected axiom in generated decomposition {theoremName}: {axiomName}"

end ModelTests
