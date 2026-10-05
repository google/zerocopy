/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy.Funs
public import SpecPrelude
public import SpecsSyntax
public import Models
public import LayoutModel
public import TraitLaws
@[expose] public section

open Aeneas Aeneas.Std
open Zerocopy.Proofs
namespace Zerocopy.Specs

check_model_inputs Zerocopy.byteorder.verification.read_u16_le with 0 type parameters
aeneas_spec_begin
spec read_u16_le_spec
  for @Zerocopy.byteorder.verification.read_u16_le with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeLE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u16_le_spec for Zerocopy.byteorder.verification.read_u16_le with 1

check_model_inputs Zerocopy.byteorder.verification.write_u16_le with 0 type parameters
aeneas_spec_begin
spec write_u16_le_spec
  for @Zerocopy.byteorder.verification.write_u16_le with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeLE 2 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u16_le_spec for Zerocopy.byteorder.verification.write_u16_le with 1

check_model_inputs Zerocopy.byteorder.verification.set_u16_le with 0 type parameters
aeneas_spec_begin
spec set_u16_le_spec
  for @Zerocopy.byteorder.verification.set_u16_le with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u16_le_spec for Zerocopy.byteorder.verification.set_u16_le with 2

check_model_inputs Zerocopy.byteorder.verification.read_u16_be with 0 type parameters
aeneas_spec_begin
spec read_u16_be_spec
  for @Zerocopy.byteorder.verification.read_u16_be with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeBE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u16_be_spec for Zerocopy.byteorder.verification.read_u16_be with 1

check_model_inputs Zerocopy.byteorder.verification.write_u16_be with 0 type parameters
aeneas_spec_begin
spec write_u16_be_spec
  for @Zerocopy.byteorder.verification.write_u16_be with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeBE 2 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u16_be_spec for Zerocopy.byteorder.verification.write_u16_be with 1

check_model_inputs Zerocopy.byteorder.verification.set_u16_be with 0 type parameters
aeneas_spec_begin
spec set_u16_be_spec
  for @Zerocopy.byteorder.verification.set_u16_be with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u16_be_spec for Zerocopy.byteorder.verification.set_u16_be with 2

check_model_inputs Zerocopy.byteorder.verification.read_u32_le with 0 type parameters
aeneas_spec_begin
spec read_u32_le_spec
  for @Zerocopy.byteorder.verification.read_u32_le with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeLE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u32_le_spec for Zerocopy.byteorder.verification.read_u32_le with 1

check_model_inputs Zerocopy.byteorder.verification.write_u32_le with 0 type parameters
aeneas_spec_begin
spec write_u32_le_spec
  for @Zerocopy.byteorder.verification.write_u32_le with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeLE 4 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u32_le_spec for Zerocopy.byteorder.verification.write_u32_le with 1

check_model_inputs Zerocopy.byteorder.verification.set_u32_le with 0 type parameters
aeneas_spec_begin
spec set_u32_le_spec
  for @Zerocopy.byteorder.verification.set_u32_le with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u32_le_spec for Zerocopy.byteorder.verification.set_u32_le with 2

check_model_inputs Zerocopy.byteorder.verification.read_u32_be with 0 type parameters
aeneas_spec_begin
spec read_u32_be_spec
  for @Zerocopy.byteorder.verification.read_u32_be with 0 type parameters
  ensures n => (n : Nat) = Rust.Bytes.decodeBE
    (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
aeneas_spec_end
check_spec_binding Zerocopy.Specs.read_u32_be_spec for Zerocopy.byteorder.verification.read_u32_be with 1

check_model_inputs Zerocopy.byteorder.verification.write_u32_be with 0 type parameters
aeneas_spec_begin
spec write_u32_be_spec
  for @Zerocopy.byteorder.verification.write_u32_be with 0 type parameters
  ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
    Rust.Bytes.encodeBE 4 (n : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_u32_be_spec for Zerocopy.byteorder.verification.write_u32_be with 1

check_model_inputs Zerocopy.byteorder.verification.set_u32_be with 0 type parameters
aeneas_spec_begin
spec set_u32_be_spec
  for @Zerocopy.byteorder.verification.set_u32_be with 0 type parameters
  ensures r => r = n
aeneas_spec_end
check_spec_binding Zerocopy.Specs.set_u32_be_spec for Zerocopy.byteorder.verification.set_u32_be with 2

check_model_inputs Zerocopy.layout.RoundingAlignAndPhase.new with 0 type parameters
aeneas_spec_begin
spec encoding_new_spec
  for @Zerocopy.layout.RoundingAlignAndPhase.new with 0 type parameters
  requires ha : (align : Nat).isPowerOfTwo
  requires hp : (phase : Nat) < (align : Nat)
  ensures encoded => encoded.align = (align : Nat) ∧ encoded.phase = (phase : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.encoding_new_spec for Zerocopy.layout.RoundingAlignAndPhase.new with 2

check_model_inputs Zerocopy.layout.RoundingAlignAndPhase.components with 0 type parameters
aeneas_spec_begin
spec encoding_components_spec
  for @Zerocopy.layout.RoundingAlignAndPhase.components with 0 type parameters
  ensures (align, phase) =>
    align.value = self.align ∧ phase.value = self.phase
aeneas_spec_end
check_spec_binding Zerocopy.Specs.encoding_components_spec for Zerocopy.layout.RoundingAlignAndPhase.components with 1

check_model_inputs Zerocopy.layout.RoundingAlignAndPhase.align with 0 type parameters
aeneas_spec_begin
spec encoding_align_spec
  for @Zerocopy.layout.RoundingAlignAndPhase.align with 0 type parameters
  ensures align => (align : Nat) = self.align
aeneas_spec_end
check_spec_binding Zerocopy.Specs.encoding_align_spec for Zerocopy.layout.RoundingAlignAndPhase.align with 1

check_model_inputs Zerocopy.layout.TrailingSliceLayout.size_offset with 1 type parameters
aeneas_spec_begin
spec size_offset_spec
  for @Zerocopy.layout.TrailingSliceLayout.size_offset with 1 type parameters
  ensures(raw) offset =>
    offset.val = self.size_base.val - self.size_base.val % (byteFormula self).align + (byteFormula self).phase
aeneas_spec_end
check_spec_binding Zerocopy.Specs.size_offset_spec for Zerocopy.layout.TrailingSliceLayout.size_offset with 2

check_model_inputs Zerocopy.layout.TrailingSliceLayout.max_trailing_bytes with 1 type parameters
aeneas_spec_begin
spec max_trailing_bytes_spec
  for @Zerocopy.layout.TrailingSliceLayout.max_trailing_bytes with 1 type parameters
  ensures(raw) r => r.map UScalar.val = (byteFormula self).capacity available_bytes.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.max_trailing_bytes_spec for Zerocopy.layout.TrailingSliceLayout.max_trailing_bytes with 3

check_model_inputs Zerocopy.layout.TrailingSliceLayoutUsize.padding_for_elems with 0 type parameters
aeneas_spec_begin
spec padding_for_elems_spec
  for @Zerocopy.layout.TrailingSliceLayoutUsize.padding_for_elems with 0 type parameters
  ensures(raw) p => (p.val + self.offset.val + elems.val * self.elem_size.val) % UScalar.size .Usize =
    (trailingFormula self).size elems.val % UScalar.size .Usize
aeneas_spec_end
check_spec_binding Zerocopy.Specs.padding_for_elems_spec for Zerocopy.layout.TrailingSliceLayoutUsize.padding_for_elems with 2

check_model_inputs Zerocopy.layout.TrailingSliceLayoutUsize.size_for_elems with 0 type parameters
aeneas_spec_begin
spec size_for_elems_spec
  for @Zerocopy.layout.TrailingSliceLayoutUsize.size_for_elems with 0 type parameters
  ensures result => result.map (fun size => (size : Nat)) =
    (ModelViews.trailingFormula self).checkedSize Usize.max (elems : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.size_for_elems_spec for Zerocopy.layout.TrailingSliceLayoutUsize.size_for_elems with 2

check_model_inputs Zerocopy.layout.SizeInfoUsize.try_to_nonzero_elem_size with 0 type parameters
aeneas_spec_begin
spec try_nonzero_spec
  for @Zerocopy.layout.SizeInfoUsize.try_to_nonzero_elem_size with 0 type parameters
  ensures(raw) r => match self with
    | .Sized size => r = some (.Sized size)
    | .SliceDst tail =>
      if tail.elem_size = 0#usize then r = none else
        ∃ t, r = some (.SliceDst t) ∧ t.offset = tail.offset ∧
          t.size_base = tail.size_base ∧
          t.size_rounding_align_and_phase = tail.size_rounding_align_and_phase ∧
          t.elem_size.val = tail.elem_size
aeneas_spec_end
check_spec_binding Zerocopy.Specs.try_nonzero_spec for Zerocopy.layout.SizeInfoUsize.try_to_nonzero_elem_size with 1

check_model_inputs Zerocopy.layout.max_elems_for_bytes with 0 type parameters
aeneas_spec_begin
spec max_elems_for_bytes_spec
  for @Zerocopy.layout.max_elems_for_bytes with 0 type parameters
  ensures(raw) (elems, used) =>
    elems.val = bytes.val / elem_size.val.val ∧ used.val = elems.val * elem_size.val.val ∧
    used ≤ bytes ∧ bytes.val < (elems.val + 1) * elem_size.val.val ∧
    (∀ n : Nat, n * elem_size.val.val ≤ bytes.val ↔ n ≤ elems.val)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.max_elems_for_bytes_spec for Zerocopy.layout.max_elems_for_bytes with 2

check_model_inputs Zerocopy.layout.DstLayout.assume_shallow_unpadded with 0 type parameters
aeneas_spec_begin
spec assume_shallow_unpadded_spec
  for @Zerocopy.layout.DstLayout.assume_shallow_unpadded with 0 type parameters
  ensures(raw) r => r.align = self.align ∧ r.size_info = self.size_info ∧ r.statically_shallow_unpadded = true
aeneas_spec_end
check_spec_binding Zerocopy.Specs.assume_shallow_unpadded_spec for Zerocopy.layout.DstLayout.assume_shallow_unpadded with 1

check_model_inputs Zerocopy.layout.DstLayout.new_zst with 0 type parameters
aeneas_spec_begin
spec new_zst_spec
  for @Zerocopy.layout.DstLayout.new_zst with 0 type parameters
  requires(raw) hp : ∀ a ∈ repr_align, a.val.val.isPowerOfTwo
  ensures(raw) r => r.align = repr_align.getD ⟨1#usize⟩ ∧
    r.size_info = .Sized 0#usize ∧ r.statically_shallow_unpadded = true
aeneas_spec_end
check_spec_binding Zerocopy.Specs.new_zst_spec for Zerocopy.layout.DstLayout.new_zst with 1

check_model_inputs Zerocopy.layout.DstLayout.for_type with 1 type parameters
aeneas_spec_begin
spec for_type_spec (size align : Usize)
  for @Zerocopy.layout.DstLayout.for_type with 1 type parameters
  requires(raw) hs : core.mem.size_of T = .ok size
  requires(raw) ha : core.mem.align_of T = .ok align
  requires(raw) hn : 0 < align.val
  ensures(raw) r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = false
aeneas_spec_end
check_spec_binding Zerocopy.Specs.for_type_spec for Zerocopy.layout.DstLayout.for_type with 1

check_model_inputs Zerocopy.layout.DstLayout.for_unpadded_type with 1 type parameters
aeneas_spec_begin
spec for_unpadded_type_spec (size align : Usize)
  for @Zerocopy.layout.DstLayout.for_unpadded_type with 1 type parameters
  requires(raw) hs : core.mem.size_of T = .ok size
  requires(raw) ha : core.mem.align_of T = .ok align
  requires(raw) hn : 0 < align.val
  ensures(raw) r => r.align.val = align ∧ r.size_info = layout.SizeInfo.Sized size ∧ r.statically_shallow_unpadded = true
aeneas_spec_end
check_spec_binding Zerocopy.Specs.for_unpadded_type_spec for Zerocopy.layout.DstLayout.for_unpadded_type with 1

check_model_inputs Zerocopy.layout.DstLayout.for_slice with 1 type parameters
aeneas_spec_begin
spec for_slice_spec (size align : Usize)
  for @Zerocopy.layout.DstLayout.for_slice with 1 type parameters
  requires(raw) hs : core.mem.size_of T = .ok size
  requires(raw) ha : core.mem.align_of T = .ok align
  requires(raw) hp : align.val.isPowerOfTwo
  ensures(raw) r => r.align.val = align ∧ r.statically_shallow_unpadded = true ∧
    ∃ tail, r.size_info = layout.SizeInfo.SliceDst tail ∧
      tail.offset = 0#usize ∧ tail.elem_size = size ∧ tail.size_base = 0#usize ∧
      tail.size_rounding_align_and_phase._0.val.val = align.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.for_slice_spec for Zerocopy.layout.DstLayout.for_slice with 1

check_model_inputs Zerocopy.layout.DstLayout.requires_static_padding with 0 type parameters
aeneas_spec_begin
spec requires_static_padding_spec
  for @Zerocopy.layout.DstLayout.requires_static_padding with 0 type parameters
  ensures(raw) r => r = !self.statically_shallow_unpadded
aeneas_spec_end
check_spec_binding Zerocopy.Specs.requires_static_padding_spec for Zerocopy.layout.DstLayout.requires_static_padding with 1

check_model_inputs Zerocopy.layout.nested_reference.round_up with 0 type parameters
aeneas_spec_begin
spec nested_round_up_spec
  for @Zerocopy.layout.nested_reference.round_up with 0 type parameters
  ensures(raw) rounded => rounded.map UScalar.val =
    if align.val = 0 then none
    else if LayoutMath.roundUp size.val align.val ≤ Usize.max
      then some (LayoutMath.roundUp size.val align.val) else none
aeneas_spec_end
check_spec_binding Zerocopy.Specs.nested_round_up_spec for Zerocopy.layout.nested_reference.round_up with 2

check_model_inputs Zerocopy.layout.nested_reference.size_for_metadata with 0 type parameters
aeneas_spec_begin
spec nested_reference_size_spec
  for @Zerocopy.layout.nested_reference.size_for_metadata with 0 type parameters
  ensures(raw) result => result.map UScalar.val =
    NestedReference.checkedSize leading.val elem_size.val leaf_align.val elems.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.nested_reference_size_spec for Zerocopy.layout.nested_reference.size_for_metadata with 4

check_model_inputs Zerocopy.layout.primitive_checks.check_primitive_layouts with 1 type parameters
aeneas_spec_begin
spec primitive_layout_checks_spec
  for @Zerocopy.layout.primitive_checks.check_primitive_layouts with 1 type parameters
  ensures _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.primitive_layout_checks_spec for Zerocopy.layout.primitive_checks.check_primitive_layouts with 1

check_model_inputs Zerocopy.layout.primitive_checks.check_empty_layout with 0 type parameters
aeneas_spec_begin
spec empty_layout_checks_spec
  for @Zerocopy.layout.primitive_checks.check_empty_layout with 0 type parameters
  ensures _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.empty_layout_checks_spec for Zerocopy.layout.primitive_checks.check_empty_layout with 1

check_model_inputs Zerocopy.layout.tail_checks.trailing_arithmetic_check with 0 type parameters
aeneas_spec_begin
spec trailing_arithmetic_check_spec
  for @Zerocopy.layout.tail_checks.trailing_arithmetic_check with 0 type parameters
  ensures(raw) _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.trailing_arithmetic_check_spec for Zerocopy.layout.tail_checks.trailing_arithmetic_check with 5

check_model_inputs Zerocopy.pointer_metadata_unit_from_elem_count with 0 type parameters
aeneas_spec_begin
spec pointer_metadata_unit_from_elem_count_spec
  for @Zerocopy.pointer_metadata_unit_from_elem_count with 0 type parameters
  ensures(raw) result => result = ()
aeneas_spec_end
check_spec_binding Zerocopy.Specs.pointer_metadata_unit_from_elem_count_spec for Zerocopy.pointer_metadata_unit_from_elem_count with 1

check_model_inputs Zerocopy.pointer_metadata_unit_to_elem_count with 0 type parameters
aeneas_spec_begin
spec pointer_metadata_unit_to_elem_count_spec
  for @Zerocopy.pointer_metadata_unit_to_elem_count with 0 type parameters
  ensures(raw) result => result.val = 0
aeneas_spec_end
check_spec_binding Zerocopy.Specs.pointer_metadata_unit_to_elem_count_spec for Zerocopy.pointer_metadata_unit_to_elem_count with 0

check_model_inputs Zerocopy.pointer_metadata_unit_size_for_metadata with 0 type parameters
aeneas_spec_begin
spec pointer_metadata_unit_size_for_metadata_spec
  for @Zerocopy.pointer_metadata_unit_size_for_metadata with 0 type parameters
  ensures(raw) result => result = match runtime_layout.size_info with
    | .Sized size => some size
    | .SliceDst _ => none
aeneas_spec_end
check_spec_binding Zerocopy.Specs.pointer_metadata_unit_size_for_metadata_spec for Zerocopy.pointer_metadata_unit_size_for_metadata with 1

check_model_inputs Zerocopy.pointer_metadata_usize_from_elem_count with 0 type parameters
aeneas_spec_begin
spec pointer_metadata_usize_from_elem_count_spec
  for @Zerocopy.pointer_metadata_usize_from_elem_count with 0 type parameters
  ensures(raw) result => result = elems
aeneas_spec_end
check_spec_binding Zerocopy.Specs.pointer_metadata_usize_from_elem_count_spec for Zerocopy.pointer_metadata_usize_from_elem_count with 1

check_model_inputs Zerocopy.pointer_metadata_usize_to_elem_count with 0 type parameters
aeneas_spec_begin
spec pointer_metadata_usize_to_elem_count_spec
  for @Zerocopy.pointer_metadata_usize_to_elem_count with 0 type parameters
  ensures(raw) result => result = metadata
aeneas_spec_end
check_spec_binding Zerocopy.Specs.pointer_metadata_usize_to_elem_count_spec for Zerocopy.pointer_metadata_usize_to_elem_count with 1

check_model_inputs Zerocopy.pointer_metadata_usize_size_for_metadata with 0 type parameters
aeneas_spec_begin
spec pointer_metadata_usize_size_for_metadata_spec
  for @Zerocopy.pointer_metadata_usize_size_for_metadata with 0 type parameters
  ensures(raw) result => result.map UScalar.val = match runtime_layout.size_info with
    | .Sized _ => none
    | .SliceDst tail => (trailingFormula tail).checkedSize Usize.max metadata.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.pointer_metadata_usize_size_for_metadata_spec for Zerocopy.pointer_metadata_usize_size_for_metadata with 2

check_model_inputs Zerocopy.trait_checks.unaligned_alignment with 1 type parameters
aeneas_spec_begin
spec unaligned_alignment_spec
  for @Zerocopy.trait_checks.unaligned_alignment with 1 type parameters
  ensures alignment => (alignment : Nat) = 1
aeneas_spec_end
check_spec_binding Zerocopy.Specs.unaligned_alignment_spec for Zerocopy.trait_checks.unaligned_alignment with 2

check_model_inputs Zerocopy.trait_checks.check_unaligned with 1 type parameters
aeneas_spec_begin
spec unaligned_check_spec
  for @Zerocopy.trait_checks.check_unaligned with 1 type parameters
  ensures _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.unaligned_check_spec for Zerocopy.trait_checks.check_unaligned with 2

check_model_inputs Zerocopy.trait_checks.unused_unaligned_bound with 1 type parameters
aeneas_spec_begin
spec unused_unaligned_bound_spec
  for @Zerocopy.trait_checks.unused_unaligned_bound with 1 type parameters
  ensures result => result = value
aeneas_spec_end
check_spec_binding Zerocopy.Specs.unused_unaligned_bound_spec for Zerocopy.trait_checks.unused_unaligned_bound with 3

check_model_inputs Zerocopy.trait_checks.check_byte_unaligned with 0 type parameters
aeneas_spec_begin
spec concrete_unaligned_check_spec
  for @Zerocopy.trait_checks.check_byte_unaligned with 0 type parameters
  ensures _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.concrete_unaligned_check_spec for Zerocopy.trait_checks.check_byte_unaligned with 0

check_model_inputs Zerocopy.trait_checks.divide_by_unaligned with 1 type parameters
aeneas_spec_begin
spec divide_by_unaligned_spec
  for @Zerocopy.trait_checks.divide_by_unaligned with 1 type parameters
  ensures result => result = x
aeneas_spec_end
check_spec_binding Zerocopy.Specs.divide_by_unaligned_spec for Zerocopy.trait_checks.divide_by_unaligned with 3

check_model_inputs Zerocopy.trait_checks.divide_by_byte_alignment with 0 type parameters
aeneas_spec_begin
spec divide_by_byte_alignment_spec
  for @Zerocopy.trait_checks.divide_by_byte_alignment with 0 type parameters
  ensures result => result = x
aeneas_spec_end
check_spec_binding Zerocopy.Specs.divide_by_byte_alignment_spec for Zerocopy.trait_checks.divide_by_byte_alignment with 1

check_model_inputs Zerocopy.trait_checks.byte_codec_roundtrip with 1 type parameters
aeneas_spec_begin
spec byte_codec_roundtrip_spec
  for @Zerocopy.trait_checks.byte_codec_roundtrip with 1 type parameters
  ensures result => result = byte
aeneas_spec_end
check_spec_binding Zerocopy.Specs.byte_codec_roundtrip_spec for Zerocopy.trait_checks.byte_codec_roundtrip with 3

check_model_inputs Zerocopy.trait_checks.forwarded_byte_codec with 0 type parameters
aeneas_spec_begin
spec forwarded_byte_codec_spec
  for @Zerocopy.trait_checks.forwarded_byte_codec with 0 type parameters
  ensures result => result = byte
aeneas_spec_end
check_spec_binding Zerocopy.Specs.forwarded_byte_codec_spec for Zerocopy.trait_checks.forwarded_byte_codec with 1

check_model_inputs Zerocopy.trait_checks.check_array_into_bytes with 0 type parameters
aeneas_spec_begin
spec array_into_bytes_spec
  for @Zerocopy.trait_checks.check_array_into_bytes with 0 type parameters
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 3#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array U8 3#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Unit 4#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 0#usize)
  ensures _ => AeneasSpecs.RustModel.initializedRepresentation
    (Aeneas.Std.Array (Aeneas.Std.Array Bool 2#usize) 3#usize)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.array_into_bytes_spec for Zerocopy.trait_checks.check_array_into_bytes with 0

check_model_inputs Zerocopy.util.bytewrite.exact with 0 type parameters
aeneas_spec_begin
spec write_exact_spec
  for @Zerocopy.util.bytewrite.exact with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length = dst.val.length) ∧
    out.2.val = if src.val.length = dst.val.length then src.val else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_exact_spec for Zerocopy.util.bytewrite.exact with 2

check_model_inputs Zerocopy.util.bytewrite.prefix with 0 type parameters
aeneas_spec_begin
spec write_prefix_spec
  for @Zerocopy.util.bytewrite.prefix with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then src.val ++ dst.val.drop src.val.length else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_prefix_spec for Zerocopy.util.bytewrite.prefix with 2

check_model_inputs Zerocopy.util.bytewrite.suffix with 0 type parameters
aeneas_spec_begin
spec write_suffix_spec
  for @Zerocopy.util.bytewrite.suffix with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then dst.val.take (dst.val.length - src.val.length) ++ src.val else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_suffix_spec for Zerocopy.util.bytewrite.suffix with 2

check_model_inputs Zerocopy.util.bytewrite.be_word_prefix with 0 type parameters
aeneas_spec_begin
spec write_be_word_prefix_spec
  for @Zerocopy.util.bytewrite.be_word_prefix with 0 type parameters
  ensures(raw) out => out.1 = decide (2 ≤ dst.val.length) ∧
    out.2.val.map (fun byte => byte.bv) = if 2 ≤ dst.val.length
      then Rust.Bytes.encodeBE 2 n.val ++ (dst.val.drop 2).map (fun byte => byte.bv)
      else dst.val.map (fun byte => byte.bv)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.write_be_word_prefix_spec for Zerocopy.util.bytewrite.be_word_prefix with 2

check_model_inputs Zerocopy.util.checks.check_arithmetic with 0 type parameters
aeneas_spec_begin
spec arithmetic_checks_spec
  for @Zerocopy.util.checks.check_arithmetic with 0 type parameters
  ensures _ => True
aeneas_spec_end
check_spec_binding Zerocopy.Specs.arithmetic_checks_spec for Zerocopy.util.checks.check_arithmetic with 2

check_model_inputs Zerocopy.util.padding_needed_for with 0 type parameters
aeneas_spec_begin
spec padding_lt_alignment
  for @Zerocopy.util.padding_needed_for with 0 type parameters
  requires h : (align : Nat).isPowerOfTwo
  ensures p => (p : Nat) < (align : Nat) ∧
    let L : Nat := len
    let A : Nat := align
    let P : Nat := p
    P = (A - L % A) % A ∧ (L + P) % A = 0 ∧
      (∀ q : Nat, (L + q) % A = 0 → P ≤ q) ∧ (P = 0 ↔ L % A = 0)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.padding_lt_alignment for Zerocopy.util.padding_needed_for with 2

check_model_inputs Zerocopy.util.round_down_to_next_multiple_of_alignment with 0 type parameters
aeneas_spec_begin
spec round_down_spec
  for @Zerocopy.util.round_down_to_next_multiple_of_alignment with 0 type parameters
  requires h : (align : Nat).isPowerOfTwo
  ensures m => (m : Nat) ≤ (n : Nat) ∧
    let N : Nat := n
    let A : Nat := align
    let M : Nat := m
    M = N - N % A ∧ M % A = 0 ∧ N < M + A ∧
      (∀ q : Nat, q ≤ N → q % A = 0 → q ≤ M)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.round_down_spec for Zerocopy.util.round_down_to_next_multiple_of_alignment with 2

check_model_inputs Zerocopy.util.max with 0 type parameters
aeneas_spec_begin
spec max_spec
  for @Zerocopy.util.max with 0 type parameters
  ensures r => (r : Nat) = max (a : Nat) (b : Nat) ∧ (r = a ∨ r = b) ∧
    (a : Nat) ≤ (r : Nat) ∧ (b : Nat) ≤ (r : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.max_spec for Zerocopy.util.max with 2

check_model_inputs Zerocopy.util.min with 0 type parameters
aeneas_spec_begin
spec min_spec
  for @Zerocopy.util.min with 0 type parameters
  ensures r => (r : Nat) = min (a : Nat) (b : Nat) ∧ (r = a ∨ r = b) ∧
    (r : Nat) ≤ (a : Nat) ∧ (r : Nat) ≤ (b : Nat)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.min_spec for Zerocopy.util.min with 2

check_model_inputs Zerocopy.util.safety_checks.checked_bool with 0 type parameters
aeneas_spec_begin
spec checked_bool_spec
  for @Zerocopy.util.safety_checks.checked_bool with 0 type parameters
  ensures(raw) r => r = if byte.val < 2 then some (decide (byte.val = 1)) else none
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_bool_spec for Zerocopy.util.safety_checks.checked_bool with 1

check_model_inputs Zerocopy.util.safety_checks.checked_copy with 0 type parameters
aeneas_spec_begin
spec checked_copy_spec
  for @Zerocopy.util.safety_checks.checked_copy with 0 type parameters
  ensures(raw) out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then src.val ++ dst.val.drop src.val.length else dst.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_copy_spec for Zerocopy.util.safety_checks.checked_copy with 2

check_model_inputs Zerocopy.util.safety_checks.checked_nonzero with 0 type parameters
aeneas_spec_begin
spec checked_nonzero_spec
  for @Zerocopy.util.safety_checks.checked_nonzero with 0 type parameters
  ensures(raw) r => match r with
    | none => n.val = 0
    | some value => value.val = n ∧ 0 < value.val.val
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_nonzero_spec for Zerocopy.util.safety_checks.checked_nonzero with 1

check_model_inputs Zerocopy.util.safety_checks.checked_bool_pair with 0 type parameters
aeneas_spec_begin
spec checked_bool_pair_spec
  for @Zerocopy.util.safety_checks.checked_bool_pair with 0 type parameters
  ensures(raw) r => match r with
    | none => ∃ byte ∈ bytes.val, 2 ≤ byte.val
    | some values => values.val = bytes.val.map (fun byte => decide (byte.val = 1)) ∧
        ∀ byte ∈ bytes.val, byte.val < 2
aeneas_spec_end
check_spec_binding Zerocopy.Specs.checked_bool_pair_spec for Zerocopy.util.safety_checks.checked_bool_pair with 1

check_model_inputs Zerocopy.util.safety_checks.bool_slice_valid with 0 type parameters
aeneas_spec_begin
spec bool_slice_valid_spec
  for @Zerocopy.util.safety_checks.bool_slice_valid with 0 type parameters
  ensures(raw) r => r = decide (∀ byte ∈ bytes.val, byte.val < 2)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.bool_slice_valid_spec for Zerocopy.util.safety_checks.bool_slice_valid with 1

check_model_inputs Zerocopy.util.validity.bool_encoding with 0 type parameters
aeneas_spec_begin
spec bool_encoding_spec
  for @Zerocopy.util.validity.bool_encoding with 0 type parameters
  ensures(raw) r => r = decide (byte.val = 0 ∨ byte.val = 1)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.bool_encoding_spec for Zerocopy.util.validity.bool_encoding with 1

check_model_inputs Zerocopy.util.validity.nonzero_encoding with 0 type parameters
aeneas_spec_begin
spec nonzero_encoding_spec
  for @Zerocopy.util.validity.nonzero_encoding with 0 type parameters
  ensures(raw) r => r = decide (n.val ≠ 0)
aeneas_spec_end
check_spec_binding Zerocopy.Specs.nonzero_encoding_spec for Zerocopy.util.validity.nonzero_encoding with 1

end Zerocopy.Specs
