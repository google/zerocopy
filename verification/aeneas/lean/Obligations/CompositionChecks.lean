/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Obligations
@[expose] public section

/-!
These independent expectations require each ordinary Rust harness to terminate
successfully, including its assertions. The premises describe the positive
NonZeroUsize representations admitted by Rust's types; numeric witnesses carry
no semantic validity requirement, since the harnesses check them themselves.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Obligations
open Zerocopy.Proofs
abbrev CompositionReferenceLayout := layout.composition_checks.ReferenceLayout

def composition_extend_checks_spec_contract (preceding field : layout.DstLayout)
    (packed : Option NonZeroUsize) (_preceding_reference _field_reference : CompositionReferenceLayout)
    (run : Result Unit) : Prop :=
  layoutValid preceding → layoutValid field → (∀ a ∈ packed, 0 < a.val.val) → run ⦃ _ => True ⦄

def composition_extend_checks_spec : Prop :=
  ∀ preceding field packed preceding_reference field_reference,
    composition_extend_checks_spec_contract preceding field packed preceding_reference field_reference
      (layout.composition_checks.check_extend preceding field packed preceding_reference field_reference)

def composition_pad_checks_spec_contract (runtime_layout : layout.DstLayout)
    (_reference : CompositionReferenceLayout) (run : Result Unit) : Prop :=
  layoutValid runtime_layout → run ⦃ _ => True ⦄

def composition_pad_checks_spec : Prop :=
  ∀ runtime_layout reference, composition_pad_checks_spec_contract runtime_layout reference
    (layout.composition_checks.check_pad runtime_layout reference)

def composition_constructor_checks_spec_contract (repr_align packed : Option NonZeroUsize)
    (fields : Slice layout.DstLayout) (_references : Slice CompositionReferenceLayout)
    (run : Result Unit) : Prop :=
  (∀ a ∈ repr_align, 0 < a.val.val) → (∀ a ∈ packed, 0 < a.val.val) →
    (∀ field ∈ fields.val, layoutValid field) → run ⦃ _ => True ⦄

def composition_constructor_checks_spec : Prop :=
  ∀ repr_align packed fields references,
    composition_constructor_checks_spec_contract repr_align packed fields references
      (layout.composition_checks.check_constructor repr_align packed fields references)

end Zerocopy.Obligations
