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
namespace ModelCompletionTests

structure Pair where
  first : Nat
  second : Nat
  ordered : first ≤ second

example (n : Nat) : Pair := model_value { first := n, second := n + 1, .. }
example (n : Nat) : Pair :=
  model_value (by exact { first := n, second := n, ordered := Nat.le_refl n })
example (n : Nat) : Pair :=
  model_value { first := n, second := n, ordered := by omega }
example (n : Nat) : Option Pair :=
  model_value (if h : n < 4 then some { first := n, second := 4, .. }
    else some { first := 4, second := n, .. })

structure Nested where
  pair : Pair
  positive : 0 < pair.second
example (n : Nat) : Nested :=
  model_value { pair := { first := n, second := n + 1, .. }, .. }

structure Encoding where
  word : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner

aeneas_model_shape Encoding with 0 type parameters begin
 model Value where
   align : Nat
   phase : Nat
   pow2 : align.isPowerOfTwo
   phase_lt : phase < align
   fits : align + phase ≤ Usize.max
end
derive_rust_model Encoding with 0 type parameters decode self =>
  let word := self.word.value
  let align := 2 ^ Nat.log2 word
  { align := align, phase := word - align, .. }
check_model_binding Encoding with 0 type parameters

-- Completion does not admit invalid children of an infallible local decoder.
example : Encoding.decode ⟨⟨0#usize⟩⟩ = none := rfl
example : (Encoding.decode ⟨⟨13#usize⟩⟩).map (fun r => (r.align, r.phase)) =
    some (8, 5) := by decide

structure Fallible where
  word : core.num.nonzero.NonZero Usize core.num.niche_types.NonZeroUsizeInner

aeneas_model_shape Fallible with 0 type parameters begin
 model Value where
   value : Nat
   positive : 0 < value
end
derive_rust_model Fallible with 0 type parameters decode? self =>
  if h : 1 < self.word.value then some { value := self.word.value - 1, .. }
  else none
check_model_binding Fallible with 0 type parameters
example : Fallible.decode ⟨⟨1#usize⟩⟩ = none := rfl
example : (Fallible.decode ⟨⟨3#usize⟩⟩).map (·.value) = some 2 := rfl

structure Impossible where
  value : Nat
aeneas_model_shape Impossible with 0 type parameters begin
 model Value where
   value : Nat
   impossible : False
end

structure PropositionData where
  claim : Prop

syntax (name := discardedCompletionFixture) "discard_completion_fixture " command : command
@[command_elab discardedCompletionFixture] meta def discardCompletionFixture :
    Lean.Elab.Command.CommandElab := fun stx =>
  Lean.withoutModifyingEnv (Lean.Elab.Command.elabCommand stx[1])

-- These check the intended failure reason without fixing incidental pretty printing.
/-- Supply the omitted data value; automatic model completion only proves propositions -/
#guard_msgs (substring := true) in
discard_completion_fixture example : Pair := model_value { second := 1, .. }

/-- Supply the omitted data value; automatic model completion only proves propositions -/
#guard_msgs (substring := true) in
discard_completion_fixture example : PropositionData := model_value { .. }

-- A false constraint never silently narrows decode? by turning failure into none.
/-- Could not prove the omitted model constraint. Supply an explicit field proof. -/
#guard_msgs (substring := true) in
discard_completion_fixture derive_rust_model Impossible with 0 type parameters decode? self =>
  some { value := self.value, .. }

-- An unresolved target type must not be guessed to be a proposition.
elab "unresolved_completion_goal" : tactic => do
  let unknownSort ← Lean.Meta.mkFreshLevelMVar
  let unknownType ← Lean.Meta.mkFreshExprMVar (some (mkSort unknownSort))
  let unknownGoal ← Lean.Meta.mkFreshExprMVar (some unknownType)
  Lean.Elab.Tactic.setGoals [unknownGoal.mvarId!]

/-- Supply the omitted data value; automatic model completion only proves propositions -/
#guard_msgs (substring := true) in
discard_completion_fixture example : True := by
  unresolved_completion_goal
  complete_model_proofs

-- Exhaustion remains a native compilation failure, including for a valid model.
/-- deterministic timeout -/
#guard_msgs (substring := true) in
discard_completion_fixture example (word : NonZeroUsizeValue) : Encoding.Value :=
  model_value (by
    let align := 2 ^ Nat.log2 word.value
    refine' { align := align, phase := word.value - align, .. }
    set_option maxHeartbeats 1 in
      complete_model_proofs)

end ModelCompletionTests
