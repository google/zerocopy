/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DropOwnership
@[expose] public section

namespace AeneasSpecs.DropOwnership.Tests

/-!
These propositions are checked by the kernel. They exercise graph ownership
and validation; raw-schema, isolation, and exact-snapshot tests belong to the
decoder and admission integration. A missing effect below models Copy; the raw
decoder must distinguish that case from unsupported or omitted syntax.
-/

def moved : Graph :=
  { nodes := [{ effects := [.consume 0], candidateDrop := some 0 }]
    localCount := 1 }

example : accepted moved = true := by decide

-- An argument still carries an obligation until a supported move consumes it.
example : accepted {
    nodes := [{ candidateDrop := some 0 }], localCount := 1 } = false := by decide

-- Copy leaves ownership unchanged, as does moving a different local.
example : accepted {
    nodes := [{ effects := [.consume 1], candidateDrop := some 0 }]
    localCount := 2 } = false := by decide

-- Whole-local definitions restore ownership, after all RHS operand effects.
example : accepted {
    nodes := [{ effects := [.consume 0, .define 0], candidateDrop := some 0 }]
    localCount := 1 } = false := by decide

-- In contrast, consuming the newly defined value really leaves the slot empty.
example : accepted {
    nodes := [{ effects := [.define 0, .consume 0], candidateDrop := some 0 }]
    localCount := 1 } = true := by decide

-- Slot reuse, storage markers, and call destinations must be definitions. They
-- cannot establish empty ownership, even after an earlier move.
example : accepted {
    nodes := [
      { effects := [.consume 0], successors := [1] },
      { effects := [.define 0], successors := [2] },
      { candidateDrop := some 0 }]
    localCount := 1 } = false := by decide

def joined (right : List Effect) : Graph :=
  { nodes := [
      { successors := [1, 2] },
      { effects := [.consume 0], successors := [3] },
      { effects := right, successors := [3] },
      { candidateDrop := some 0 }]
    localCount := 1 }

-- Every incoming branch must establish emptiness. Taking union at a join
-- preserves the obligation from an ordinary or exceptional failure path.
example : accepted (joined []) = false := by decide
example : accepted (joined [.consume 0]) = true := by decide
example : accepted (joined [.consume 0, .define 0]) = false := by decide

-- A call defines its destination on normal and unwind successors alike. Its
-- preceding argument move does not justify dropping that destination.
example : accepted {
    nodes := [
      { effects := [.consume 0, .define 0], successors := [1, 2] },
      {},
      { candidateDrop := some 0 }]
    localCount := 1 } = false := by decide

-- A disconnected component is independently seeded with every declared local.
example : accepted {
    nodes := [
      { effects := [.consume 0], candidateDrop := some 0 },
      { candidateDrop := some 0 }]
    localCount := 1 } = false := by decide

example : accepted {
    nodes := [
      { effects := [.consume 0], candidateDrop := some 0 },
      { effects := [.consume 0], candidateDrop := some 0 }]
    localCount := 1 } = true := by decide

-- A designated entry is seeded even when it also has incoming edges. The
-- body's entry cannot inherit a move from a disconnected predecessor.
example : accepted {
    nodes := [
      { effects := [.consume 0], successors := [1] },
      { candidateDrop := some 0 }]
    localCount := 1, entry := 1 } = false := by decide

-- Reject cycles everywhere, including disconnected components without drops.
example : accepted {
    nodes := [
      { effects := [.consume 0], candidateDrop := some 0 },
      { successors := [2] },
      { successors := [1] }]
    localCount := 1 } = false := by decide

example : accepted {
    nodes := [{
      effects := [.consume 0]
      candidateDrop := some 0
      successors := [0] }]
    localCount := 1 } = false := by decide

-- No invalid graph can gain acceptance through an empty iteration or default
-- lookup. This includes the entry, successors, move/define operands, and drops.
example : accepted { nodes := [], localCount := 1 } = false := by decide
example : accepted { nodes := [{}], localCount := 0, entry := 1 } = false := by decide
example : accepted {
    nodes := [{ successors := [1] }], localCount := 0 } = false := by decide
example : accepted {
    nodes := [{ effects := [.consume 1], candidateDrop := some 0 }]
    localCount := 1 } = false := by decide
example : accepted {
    nodes := [{ effects := [.define 1] }], localCount := 1 } = false := by decide
example : accepted {
    nodes := [{ candidateDrop := some 1 }], localCount := 1 } = false := by decide
example : accepted {
    nodes := [{ candidateDrop := some 0 }], localCount := 0 } = false := by decide

-- Untrusted certificates cannot remove initial obligations or forget an
-- obligation when propagating an edge. This does not depend on `infer`.
example : check {
    nodes := [{ candidateDrop := some 0 }], localCount := 1 }
    (fun _ => []) = false := by decide

example : check {
    nodes := [{ successors := [1] }, { candidateDrop := some 0 }]
    localCount := 1 }
    (fun index => if index = 0 then [0] else []) = false := by decide

-- Instantiate the semantic theorem with an arbitrary concrete initial state.
-- No test assumes the empty state that it is supposed to establish.
example (owns : Concrete) (declared : ∀ slot, owns slot → slot < 1) :
    ¬ execute [.consume 0] owns 0 := by
  have reached : Reachable moved 0 owns :=
    .root 0 owns (by decide) (Or.inl rfl) declared
  exact accepted_drop_empty (by decide : accepted moved = true) reached rfl

example (owns : Concrete) (declared : ∀ slot, owns slot → slot < 1)
    (outcome : DropOutcome) (after : Concrete) :
    ConditionalDrop 0 (execute [.consume 0] owns) outcome after ↔
      outcome = .silent ∧ after = execute [.consume 0] owns := by
  have reached : Reachable moved 0 owns :=
    .root 0 owns (by decide) (Or.inl rfl) declared
  exact accepted_drop_noop (by decide : accepted moved = true) reached rfl

end AeneasSpecs.DropOwnership.Tests
