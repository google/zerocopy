/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import MathViews
public import LayoutMath
@[expose] public section

/-!
Extracted records contain machine words and compressed rounding encodings.
This module gives those records ordinary mathematical observations: a size
formula, a physical slice offset, field placement, and cast or metadata
outcomes. The definitions do not call an extracted operation or assume that
it is correct.

Proofs uses the raw observations to state implementation lemmas and
independent expectations. ModelViews exposes corresponding observations of
recursively decoded mathematical records for inline clauses.
ModelProjectionLaws proves the connection when decoding succeeds. Keeping
physical offset separate from normalized base and phase is essential: inner
padding can make them differ.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

/- Read the raw trailing record as a complete-size formula over byte counts. The
compressed word determines alignment and phase; physical offset is retained.
-/
def byteFormula {E : Type} (self : layout.TrailingSliceLayout E) : LayoutMath.Formula :=
  let code := self.size_rounding_align_and_phase._0.val.val
  let align := 2 ^ Nat.log2 code
  ⟨self.size_base.val, code - align, align, 0, self.offset.val⟩

/- Specialize the byte formula to the raw element stride used by usize metadata.
-/
def trailingFormula (self : layout.TrailingSliceLayout Usize) : LayoutMath.Formula :=
  { byteFormula self with elem := self.elem_size.val }

/- An absent packing bound acts as the largest representable power of two. The
alignment domain bounds ensure that taking the minimum leaves an admitted
field alignment unchanged in that case.
-/
def packingValue (packed : Option NonZeroUsize) : Nat :=
  (packed.map (fun a => a.val.val)).getD (2 ^ (System.Platform.numBits - 1))

def fieldAlignment (field : layout.DstLayout) (packed : Option NonZeroUsize) : Nat :=
  min field.align.val.val (packingValue packed)

/- Round the current fixed size to the field's effective placement alignment.
-/
def placement (size : Usize) (field : layout.DstLayout) (packed : Option NonZeroUsize) :=
  LayoutMath.roundUp size.val (fieldAlignment field packed)

def castSide (cast : layout.CastType) (length : Nat) : Nat :=
  match cast with | .Prefix => 0 | .Suffix => length

def castSplit (cast : layout.CastType) (length size : Nat) : Nat :=
  match cast with | .Prefix => size | .Suffix => length - size

/- Describe exact cast outcomes independently of the implementation. Alignment
errors have priority; a suffix checks the end address; successful trailing
casts return the greatest fitting metadata and the corresponding physical
split.
-/
def castSpec (self : layout.DstLayout) (addr length : Nat) (cast : layout.CastType)
    (result : core.result.Result (Usize × Usize) layout.MetadataCastError) : Prop :=
  let anchor := addr + castSide cast length
  match result with
  | .Err .Alignment => anchor % self.align.val.val ≠ 0
  | .Err .Size => anchor % self.align.val.val = 0 ∧
    match self.size_info with
    | .Sized size => length < size.val
    | .SliceDst tail => ∀ n : Nat, length < (trailingFormula tail).size n
  | .Ok (elems, split) => anchor % self.align.val.val = 0 ∧
    match self.size_info with
    | .Sized size => elems.val = 0 ∧ size.val ≤ length ∧
      split.val = castSplit cast length size.val
    | .SliceDst tail => (trailingFormula tail).size elems.val ≤ length ∧
      (∀ n : Nat, (trailingFormula tail).size n ≤ length ↔ n ≤ elems.val) ∧
      split.val = castSplit cast length ((trailingFormula tail).size elems.val)

/- Describe exact-size metadata, including failure when no count has that
complete size. On a rounding plateau, success must select the greatest count;
fixed layouts and zero element strides have no inferred trailing metadata.
-/
def metadataSpec (self : layout.DstLayout) (size : Nat) (r : Option Usize) : Prop :=
  match self.size_info with
  | .Sized _ => r = none
  | .SliceDst tail =>
    if tail.elem_size.val = 0 then r = none else
    match r with
    | none => ∀ n : Nat, (trailingFormula tail).size n ≠ size
    | some elems => (trailingFormula tail).size elems.val = size ∧
      (∀ n : Nat, (trailingFormula tail).size n ≤ size ↔ n ≤ elems.val)

/- A selected plan maps element counts, not byte offsets. Sized variants ignore
the source count; the affine variant retains both of its numerical parameters.
-/
def castPlanMetadata (plan : layout.cast_from.CastPlan) (count : Nat) : Nat :=
  match plan with
  | .UnsizedToUnsized base multiple => base.val + count * multiple.val
  | .SizedToUnsized metadata => metadata.val
  | .SizedToSized => 0

def castMetadataFits (plan : layout.cast_from.CastPlan) (count : Nat) : Prop :=
  castPlanMetadata plan count ≤ Usize.max

/- Complete sizes use exactly the same layout observations as the independent
record semantics. This is distinct from the physical trailing-field offset.
-/
def completeLayoutSize (self : layout.DstLayout) (count : Nat) : Nat :=
  match self.size_info with
  | .Sized size => size.val
  | .SliceDst tail => (trailingFormula tail).size count

/- Acceptance certifies alignment and a size-preserving map for every count.
Rejection deliberately makes no completeness claim: the selector recognizes
sufficient conditions and may reject equivalent layouts. Variant compatibility,
positive destination stride and the exact stride ratio are retained explicitly,
so subsequent proofs can derive arithmetic bounds without assuming them.
-/
def castPlanSpec (src dst : layout.DstLayout)
    (result : Option layout.cast_from.CastPlan) : Prop :=
  match result with
  | none => True
  | some plan =>
    dst.align.val.val ≤ src.align.val.val ∧
    (match src.size_info, dst.size_info, plan with
    | .Sized srcSize, .Sized dstSize, .SizedToSized => srcSize = dstSize
    | .Sized srcSize, .SliceDst dstTail, .SizedToUnsized metadata =>
      0 < dstTail.elem_size.val ∧ (trailingFormula dstTail).size metadata.val = srcSize.val
    | .SliceDst srcTail, .SliceDst dstTail, .UnsizedToUnsized base multiple =>
      0 < dstTail.elem_size.val ∧ srcTail.elem_size.val = multiple.val * dstTail.elem_size.val ∧
        ∀ count : Nat, (trailingFormula srcTail).size count =
          (trailingFormula dstTail).size (base.val + count * multiple.val)
    | _, _, _ => False)

/- Project the raw record to the fragment vocabulary used by layout operations.
This preserves alignment, payload, physical offset, stride, and unpadded
flag.
-/
def layoutValue (self : layout.DstLayout) : LayoutMath.LayoutValue :=
  { align := self.align.val.val,
    payload := match self.size_info with
      | .Sized size => .fixed size.val
      | .SliceDst tail => .trailing (trailingFormula tail),
    unpadded := self.statically_shallow_unpadded }

/- Require the nonzero compressed rounding word in a trailing payload. Sized
fragments have no rounding encoding to validate.
-/
def canonicalLayout (self : layout.DstLayout) : Prop :=
  match self.size_info with
  | .Sized _ => True
  | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val

/- The selected Rust layout premise bounds power-of-two alignments at 2^29. This
is an explicit operation domain, not a consequence of NonZeroUsize alone.
-/
def alignmentDomain (a : Nat) : Prop := a.isPowerOfTwo ∧ a ≤ 2 ^ 29

/- Compute the independent prefix state for a constructor loop iteration.
-/
def constructionPrefix (fields : Slice layout.DstLayout) (initial : LayoutMath.LayoutValue)
    (packed : Option NonZeroUsize) (i : Nat) : LayoutMath.LayoutValue :=
  LayoutMath.LayoutValue.prefixValue (fields.val.map layoutValue) initial (packingValue packed) i

/- Require every intermediate append to fit before promising that the entire
record constructor terminates. Its final padding bound is stated separately.
-/
def constructionDomain (fields : Slice layout.DstLayout) (initial : LayoutMath.LayoutValue)
    (packed : Option NonZeroUsize) : Prop :=
  ∀ i (hi : i < fields.val.length),
    alignmentDomain (constructionPrefix fields initial packed i).align ∧
    alignmentDomain fields.val[i].align.val.val ∧ canonicalLayout fields.val[i] ∧
    (constructionPrefix fields initial packed i).extendFits
      (layoutValue fields.val[i]) (packingValue packed) Usize.max

def initialAlignment (repr_align : Option NonZeroUsize) : Nat :=
  (repr_align.map (fun a => a.val.val)).getD 1

attribute [contract_simps] castSide castSplit castSpec metadataSpec

end Zerocopy.Proofs

-- Mathematical projections consume the one recursively decoded record. The
-- raw projections above remain for independently stated representation claims.
namespace Zerocopy.ModelViews
open AeneasSpecs

/- Read the decoded mathematical trailing record as a complete-size formula over
byte counts. Alignment and phase have already been decoded; physical offset
remains a separate observation.
-/
def byteFormula {EModel : Type}
    (self : layout.TrailingSliceLayout.Fields EModel) : LayoutMath.Formula :=
  let rounding := self.size_rounding_align_and_phase
  ⟨self.size_base.value, rounding.phase, rounding.align, 0, self.offset.value⟩

/- Specialize the byte formula to the decoded bounded element stride used by
usize metadata.
-/
def trailingFormula (self : layout.TrailingSliceLayout.Fields (UnsignedWord .Usize)) : LayoutMath.Formula :=
  { byteFormula self with elem := self.elem_size.value }

/- An absent packing bound acts as the largest representable power of two. The
alignment domain bounds ensure that taking the minimum leaves an admitted
field alignment unchanged in that case.
-/
def packingValue (packed : Option NonZeroUsizeValue) : Nat :=
  (packed.map (fun a => a.value)).getD (2 ^ (System.Platform.numBits - 1))

def fieldAlignment (field : layout.DstLayout.Fields) (packed : Option NonZeroUsizeValue) : Nat :=
  min field.align.value (packingValue packed)

/- Round the current fixed size to the field's effective placement alignment.
-/
def placement (size : UnsignedWord .Usize) (field : layout.DstLayout.Fields)
    (packed : Option NonZeroUsizeValue) : Nat :=
  LayoutMath.roundUp size.value (fieldAlignment field packed)

/- Project the decoded record to the fragment vocabulary used by layout
operations, preserving alignment, payload, physical offset, stride and flag.
-/
def layoutValue (self : layout.DstLayout.Fields) : LayoutMath.LayoutValue :=
  { align := self.align.value,
    payload := match self.size_info with
      | .Sized size => .fixed size.value
      | .SliceDst tail => .trailing (trailingFormula tail),
    unpadded := self.statically_shallow_unpadded }

/- Compute a constructor prefix from decoded mathematical field records.
-/
def constructionPrefix (fields : List layout.DstLayout.Fields)
    (initial : LayoutMath.LayoutValue) (packed : Option NonZeroUsizeValue)
    (i : Nat) : LayoutMath.LayoutValue :=
  LayoutMath.LayoutValue.prefixValue (fields.map layoutValue) initial (packingValue packed) i

def initialAlignment (repr_align : Option NonZeroUsizeValue) : Nat :=
  (repr_align.map (fun a => a.value)).getD 1

end Zerocopy.ModelViews

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
