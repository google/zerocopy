/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
@[expose] public section

/-!
Independent expectations for selected cast operations. Each contract describes
an arbitrary execution outcome; its unsuffixed alias supplies the actual call.
The numerical and layout domains are stated over the raw words and records.
-/
open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Obligations
open Zerocopy.Proofs

def cast_size_sequences_spec_contract (src dst : layout.TrailingSliceLayout Usize)
    (dst_base : Usize) (run : Result Bool) : Prop :=
  0 < src.size_rounding_align_and_phase._0.val.val →
  0 < dst.size_rounding_align_and_phase._0.val.val →
  0 < dst.elem_size.val → src.elem_size.val % dst.elem_size.val = 0 →
    run ⦃ same => same = true → ∀ count : Nat,
      (trailingFormula src).size count =
        (trailingFormula dst).size
          (dst_base.val + count * (src.elem_size.val / dst.elem_size.val)) ⦄

def cast_size_sequences_spec : Prop :=
  ∀ src dst dst_base, cast_size_sequences_spec_contract src dst dst_base
    (layout.cast_from.CastPlan.size_sequences_match src dst dst_base)

def cast_plan_spec_contract (src dst : layout.DstLayout)
    (run : Result (Option layout.cast_from.CastPlan)) : Prop :=
  0 < src.align.val.val → 0 < dst.align.val.val →
  canonicalLayout src → canonicalLayout dst →
    run ⦃ result => match result with
    | none => True
    | some plan =>
      dst.align.val.val ≤ src.align.val.val ∧
      (match src.size_info, dst.size_info, plan with
      | .Sized srcSize, .Sized dstSize, .SizedToSized => srcSize = dstSize
      | .Sized srcSize, .SliceDst dstTail, .SizedToUnsized metadata =>
        0 < dstTail.elem_size.val ∧
          (trailingFormula dstTail).size metadata.val = srcSize.val
      | .SliceDst srcTail, .SliceDst dstTail, .UnsizedToUnsized base multiple =>
        0 < dstTail.elem_size.val ∧
          srcTail.elem_size.val = multiple.val * dstTail.elem_size.val ∧
          ∀ count : Nat, (trailingFormula srcTail).size count =
            (trailingFormula dstTail).size (base.val + count * multiple.val)
      | _, _, _ => False) ⦄

def cast_plan_spec : Prop :=
  ∀ src dst, cast_plan_spec_contract src dst
    (layout.cast_from.CastPlan.try_compute src dst)

def cast_metadata_spec_contract (self : layout.cast_from.CastPlan) (src_meta : Usize)
    (run : Result Usize) : Prop :=
  castPlanMetadata self src_meta.val ≤ Usize.max →
    run ⦃ metadata => metadata.val = castPlanMetadata self src_meta.val ⦄

def cast_metadata_spec : Prop :=
  ∀ self src_meta, cast_metadata_spec_contract self src_meta
    (layout.cast_from.CastPlan.cast_metadata self src_meta)

def add_scaled_metadata_spec_contract (base metadata multiple : Usize)
    (run : Result Usize) : Prop :=
  base.val + metadata.val * multiple.val ≤ Usize.max →
    run ⦃ result => result.val = base.val + metadata.val * multiple.val ⦄

def add_scaled_metadata_spec : Prop :=
  ∀ base metadata multiple, add_scaled_metadata_spec_contract base metadata multiple
    (layout.add_scaled_metadata base metadata multiple)

end Zerocopy.Obligations
