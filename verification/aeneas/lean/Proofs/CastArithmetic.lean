/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
@[expose] public section

open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

/- The complete affine bound implies representability of both intermediate
operations. On that domain the concrete unchecked-operation models use the
backend's checked arithmetic and return exactly the natural-number result.
-/
theorem add_scaled_metadata_spec (base metadata multiple : Usize)
    (fits : base.val + metadata.val * multiple.val ≤ Usize.max) :
    layout.add_scaled_metadata base metadata multiple
      ⦃ result => result.val = base.val + metadata.val * multiple.val ⦄ := by
  unfold layout.add_scaled_metadata
  have productFits : metadata.val * multiple.val ≤ Usize.max := by omega
  simp only [core.num.Usize.unchecked_mul, productFits, if_true]
  step with Usize.mul_spec (x := metadata) (y := multiple) (by omega) as ⟨scaled, hscaled⟩
  have sumFits : base.val + scaled.val ≤ Usize.max := by rw [hscaled]; exact fits
  simp only [core.num.Usize.unchecked_add, sumFits, if_true]
  step with Usize.add_spec (x := base) (y := scaled)
    (by rw [hscaled]; exact fits) as ⟨result, hresult⟩
  simpa only [WP.spec_ok, hscaled] using hresult

/- Every plan variant follows its numerical map. Only the affine variant
needs an arithmetic bound; the other variants return their literal metadata.
-/
theorem cast_metadata_spec (self : layout.cast_from.CastPlan) (src_meta : Usize)
    (fits : castMetadataFits self src_meta.val) :
    layout.cast_from.CastPlan.cast_metadata self src_meta
      ⦃ metadata => metadata.val = castPlanMetadata self src_meta.val ⦄ := by
  cases self with
  | UnsizedToUnsized base multiple =>
      exact add_scaled_metadata_spec base src_meta multiple fits
  | SizedToUnsized metadata =>
      simp [layout.cast_from.CastPlan.cast_metadata, castPlanMetadata]
  | SizedToSized =>
      simp [layout.cast_from.CastPlan.cast_metadata, castPlanMetadata]

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs
open AeneasSpecs

theorem add_scaled_metadata_spec : Zerocopy.Specs.add_scaled_metadata_spec := by
  unfold Zerocopy.Specs.add_scaled_metadata_spec
  representation_simps
  intro base metadata multiple fits
  exact Raw.add_scaled_metadata_spec base metadata multiple fits
register_spec_step add_scaled_metadata_spec

theorem cast_metadata_spec : Zerocopy.Specs.cast_metadata_spec := by
  unfold Zerocopy.Specs.cast_metadata_spec
  representation_simps
  intro self src_meta _validity fits
  exact Raw.cast_metadata_spec self src_meta fits
register_spec_step cast_metadata_spec

end Zerocopy.Proofs
