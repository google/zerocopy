/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
public import CastMath
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs

/- A successful selector certificate retains the alignment ordering directly.
No additional layout validity premise is needed to project that fact.
-/
theorem castPlanSpec_alignment (src dst : layout.DstLayout)
    (plan : layout.cast_from.CastPlan)
    (hplan : castPlanSpec src dst (some plan)) :
    dst.align.val.val ≤ src.align.val.val := hplan.1

/- Variant compatibility in the certificate rules out the nine unsupported
combinations. Each supported variant preserves complete size for every natural
source count; this is independent of machine representability.
-/
theorem castPlanSpec_size (src dst : layout.DstLayout)
    (plan : layout.cast_from.CastPlan)
    (hplan : castPlanSpec src dst (some plan)) (count : Nat) :
    completeLayoutSize src count =
      completeLayoutSize dst (castPlanMetadata plan count) := by
  cases hs : src.size_info <;> cases hd : dst.size_info <;> cases plan <;>
    simp only [castPlanSpec, hs, hd, and_false] at hplan <;> try contradiction
  all_goals simp only [completeLayoutSize, hs, hd, castPlanMetadata]
  · rw [hplan.2]
  · exact hplan.2.2.symm
  · exact hplan.2.2.2 count

/- A fitting complete source size bounds the numerical metadata map. For an
affine plan, affine_metadata_fits supplies both its product and sum bounds;
the sum is precisely castMetadataFits. Destination-stride positivity is
already retained by the certificate, rather than assumed by this theorem.
-/
theorem castPlanSpec_metadata_fits (src dst : layout.DstLayout)
    (plan : layout.cast_from.CastPlan)
    (hplan : castPlanSpec src dst (some plan)) (count : Nat)
    (hfit : completeLayoutSize src count ≤ Usize.max) :
    castMetadataFits plan count := by
  cases hs : src.size_info <;> cases hd : dst.size_info <;> cases plan <;>
    simp only [castPlanSpec, hs, hd, and_false] at hplan <;> try contradiction
  all_goals simp only [completeLayoutSize, hs] at hfit
  all_goals simp only [castMetadataFits, castPlanMetadata]
  · exact Nat.zero_le _
  · apply Nat.le_trans ((trailingFormula _).metadata_le_size _ hplan.2.1)
    rw [hplan.2.2]
    exact hfit
  · exact (LayoutMath.affine_metadata_fits _ _ _ _ count Usize.max
      hplan.2.1 (hplan.2.2.2 count) hfit).2

end Zerocopy.Proofs
