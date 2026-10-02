/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import LayoutMath
@[expose] public section

/-!
Extracted trailing records contain machine words and compressed rounding
encodings. This module interprets those records as an unbounded complete-size
formula and a separately observed physical slice offset. Its definitions do
not call an extracted operation or assume that an operation is correct.

Keeping physical offset separate from normalized base and phase is essential:
inner padding can make them differ. Operation proofs use these observations
to connect extracted arithmetic with the independent layout mathematics.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs


end Zerocopy.Proofs

namespace Zerocopy.Proofs.NestedReference

/- The independent recursive rule uses unbounded arithmetic and complete
inner-field sizes. Layers are ordered from outermost to innermost. These
definitions do not call an extracted implementation or manipulate its
normalized base and phase.
-/
def layerValid (layer : layout.nested_reference.NestedLayer) : Prop :=
  layer.packed.val.isPowerOfTwo ∧ layer.min_align.val.isPowerOfTwo ∧
    layer.min_align.val ≤ layer.packed.val

def valid (layers : List layout.nested_reference.NestedLayer)
    (elem alignment : Nat) : Prop :=
  alignment.isPowerOfTwo ∧ elem % alignment = 0 ∧ ∀ layer ∈ layers, layerValid layer

def step (layer : layout.nested_reference.NestedLayer) (inner : Nat × Nat) : Nat × Nat :=
  let placementAlign := min inner.2 layer.packed.val
  let alignment := max layer.min_align.val placementAlign
  (LayoutMath.roundUp (LayoutMath.roundUp layer.prefix_bytes.val placementAlign + inner.1) alignment,
    alignment)

def state (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata : Nat) : Nat × Nat :=
  layers.foldr step (metadata * elem, alignment)

theorem state_cons (layer : layout.nested_reference.NestedLayer)
    (layers : List layout.nested_reference.NestedLayer) (elem alignment metadata : Nat) :
    state (layer :: layers) elem alignment metadata =
      step layer (state layers elem alignment metadata) := rfl

theorem step_contains_inner (layer : layout.nested_reference.NestedLayer) (inner : Nat × Nat) :
    inner.1 ≤ (step layer inner).1 := by
  simp only [step, LayoutMath.roundUp]
  omega

theorem step_alignment_power (layer : layout.nested_reference.NestedLayer)
    (inner : Nat × Nat) (hl : layerValid layer) (ha : inner.2.isPowerOfTwo) :
    (step layer inner).2.isPowerOfTwo := by
  simp only [step]
  have hm : (min inner.2 layer.packed.val).isPowerOfTwo := by
    by_cases h : inner.2 ≤ layer.packed.val
    · simpa only [Nat.min_eq_left h] using ha
    · simpa only [Nat.min_eq_right (by omega : layer.packed.val ≤ inner.2)] using hl.1
  by_cases h : layer.min_align.val ≤ min inner.2 layer.packed.val
  · simpa only [Nat.max_eq_right h] using hm
  · simpa only [Nat.max_eq_left (by omega : min inner.2 layer.packed.val ≤ layer.min_align.val)]
      using hl.2.1

theorem state_alignment_power (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata : Nat) (h : valid layers elem alignment) :
    (state layers elem alignment metadata).2.isPowerOfTwo := by
  induction layers with
  | nil => exact h.1
  | cons layer layers ih =>
    simp only [state, List.foldr_cons]
    apply step_alignment_power
    · exact h.2.2 layer (by simp)
    · apply ih
      exact ⟨h.1, h.2.1, fun x hx => h.2.2 x (by simp [hx])⟩

theorem state_alignment_bound (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata bound : Nat) (ha : alignment ≤ bound)
    (hl : ∀ layer ∈ layers, layer.min_align.val ≤ bound) :
    (state layers elem alignment metadata).2 ≤ bound := by
  induction layers with
  | nil => exact ha
  | cons layer layers ih =>
    rw [state_cons]
    simp only [step]
    apply max_le
    · exact hl layer (by simp)
    · apply le_trans (Nat.min_le_left _ _)
      exact ih (fun x hx => hl x (by simp [hx]))

theorem state_contains_suffix (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata count : Nat) :
    (state (layers.drop count) elem alignment metadata).1 ≤
      (state layers elem alignment metadata).1 := by
  induction layers generalizing count with
  | nil => simp
  | cons layer layers ih =>
    cases count with
    | zero => simp
    | succ count =>
      simp only [List.drop_succ_cons, state_cons]
      exact le_trans (ih count) (step_contains_inner layer (state layers elem alignment metadata))

theorem suffix_zero_size_fits (layers : List layout.nested_reference.NestedLayer)
    (elem alignment limit count : Nat) (hfit : (state layers elem alignment 0).1 ≤ limit) :
    (state (layers.drop count) elem alignment 0).1 ≤ limit :=
  le_trans (state_contains_suffix layers elem alignment 0 count) hfit

theorem step_contains_placed_field (layer : layout.nested_reference.NestedLayer)
    (inner : Nat × Nat) :
    LayoutMath.roundUp layer.prefix_bytes.val (min inner.2 layer.packed.val) + inner.1 ≤
      (step layer inner).1 := by
  simp only [step, LayoutMath.roundUp]
  omega

theorem step_contains_prefix (layer : layout.nested_reference.NestedLayer)
    (inner : Nat × Nat) : layer.prefix_bytes.val ≤ (step layer inner).1 := by
  simp only [step, LayoutMath.roundUp]
  omega

theorem valid_cons (layer : layout.nested_reference.NestedLayer)
    (layers : List layout.nested_reference.NestedLayer) (elem alignment : Nat) :
    valid (layer :: layers) elem alignment ↔ layerValid layer ∧ valid layers elem alignment := by
  simp only [valid, List.mem_cons, forall_eq_or_imp]
  tauto

noncomputable def checkedState (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata : Nat) : Option (Nat × Nat) := by
  classical
  exact if valid layers elem alignment then
    if (state layers elem alignment metadata).1 ≤ Usize.max
      then some (state layers elem alignment metadata) else none
    else none

noncomputable def checkedLayer (layer : layout.nested_reference.NestedLayer)
    (inner : Option (Nat × Nat)) : Option (Nat × Nat) := by
  classical
  exact if layerValid layer then inner.bind (fun inner =>
    if (step layer inner).1 ≤ Usize.max then some (step layer inner) else none) else none

theorem checkedState_cons (layer : layout.nested_reference.NestedLayer)
    (layers : List layout.nested_reference.NestedLayer) (elem alignment metadata : Nat) :
    checkedState (layer :: layers) elem alignment metadata =
      checkedLayer layer (checkedState layers elem alignment metadata) := by
  classical
  by_cases hl : layerValid layer
  · by_cases hv : valid layers elem alignment
    · by_cases hf : (state layers elem alignment metadata).1 ≤ Usize.max
      · simp only [checkedState, checkedLayer, valid_cons, hl, hv, true_and, if_true,
          hf, state_cons, Option.bind_some]
      · have ho : ¬(step layer (state layers elem alignment metadata)).1 ≤ Usize.max := by
          have := step_contains_inner layer (state layers elem alignment metadata)
          omega
        simp only [checkedState, checkedLayer, valid_cons, hl, hv, true_and, if_true,
          hf, if_false, state_cons, ho, Option.bind_none]
    · simp only [checkedState, checkedLayer, valid_cons, hl, hv, true_and, if_false,
        if_true, Option.bind_none]
  · simp only [checkedState, checkedLayer, valid_cons, hl, false_and, if_false]

theorem checkedState_some (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata : Nat) (out : Nat × Nat)
    (h : checkedState layers elem alignment metadata = some out) :
    valid layers elem alignment ∧ state layers elem alignment metadata = out ∧ out.1 ≤ Usize.max := by
  classical
  unfold checkedState at h
  split at h
  · rename_i hv
    split at h
    · rename_i hf
      have heq := Option.some.inj h
      exact ⟨hv, heq, heq ▸ hf⟩
    · contradiction
  · contradiction

theorem checkedState_drop (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata i : Nat) (hi : i < layers.length) :
    checkedState (layers.drop i) elem alignment metadata =
      checkedLayer layers[i] (checkedState (layers.drop (i + 1)) elem alignment metadata) := by
  rw [List.drop_eq_getElem_cons hi, checkedState_cons]

noncomputable def checkedSize (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata : Nat) : Option Nat := by
  classical
  exact if valid layers elem alignment then
    if (state layers elem alignment metadata).1 ≤ Usize.max
      then some (state layers elem alignment metadata).1 else none
    else none

theorem checkedSize_eq_map (layers : List layout.nested_reference.NestedLayer)
    (elem alignment metadata : Nat) :
    checkedSize layers elem alignment metadata =
      (checkedState layers elem alignment metadata).map Prod.fst := by
  classical
  unfold checkedSize checkedState
  split <;> (try split) <;> simp

end Zerocopy.Proofs.NestedReference
