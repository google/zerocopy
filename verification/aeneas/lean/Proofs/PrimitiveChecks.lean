/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Proofs
public import Proofs.TailReference
@[expose] public section

/-!
These proofs compose the constructor contracts to check the Rust assertions.
The size and alignment inputs retain the audited ABI-read interpretations;
the harness itself supplies the visible power-of-two admission condition.
-/
open Aeneas Aeneas.Std
namespace Zerocopy.Proofs.Raw

theorem primitive_layout_checks (T : Type) :
    layout.primitive_checks.check_primitive_layouts T ⦃ _ => True ⦄ := by
  classical
  let size : Usize := if T = Usize then
    { bv := BitVec.ofNat _ (System.Platform.numBits / 8) } else RustLayout.size T
  let align : Usize := RustLayout.align T
  have hs : core.mem.size_of T = .ok size := rfl
  have ha : core.mem.align_of T = .ok align := rfl
  unfold layout.primitive_checks.check_primitive_layouts
  rw [hs, ha]
  simp only [bind_ok]
  step as ⟨enabled, he⟩
  split
  · rename_i yes
    have power : align.val.isPowerOfTwo := Eq.mp he yes
    have positive := Nat.pos_of_isPowerOfTwo power
    step with for_type_spec T size align hs ha positive as ⟨fixed, hf, hfs, hfp⟩
    simp [core.num.nonzero.NonZero.get, hf, hfs, hfp, align, size, massert]
    step with for_unpadded_type_spec T size align hs ha positive as ⟨unpadded, hu, hus, hup⟩
    simp [hu, hus, hup, align]
    step with for_slice_spec T size align hs ha power as ⟨slice, hsa, hsp, tail, hsi, ho, hel, hb, hc⟩
    simp [hsa, hsp, hsi, ho, hel, hb, align]
    have same : tail.size_rounding_align_and_phase._0.val = align :=
      UScalar.eq_of_val_eq hc
    simp [same, align]
  · simp only [WP.spec_ok]

theorem empty_layout_checks (repr_align : Option NonZeroUsize) :
    layout.primitive_checks.check_empty_layout repr_align ⦃ _ => True ⦄ := by
  unfold layout.primitive_checks.check_empty_layout
  cases repr_align with
  | none =>
    simp only [core.num.nonzero.NonZero.get, bind_ok]
    step as ⟨enabled, he⟩
    split
    · step with new_zst_spec none (by simp) as ⟨empty, ha, hs, hp⟩
      simp [ha, hs, hp, massert, UScalar.val]
    · simp only [WP.spec_ok]
  | some align =>
    simp only [core.num.nonzero.NonZero.get, bind_ok]
    step as ⟨enabled, he⟩
    split
    · rename_i yes
      have power : align.val.val.isPowerOfTwo := Eq.mp he yes
      step with new_zst_spec (some align) (by simpa using power) as ⟨empty, ha, hs, hp⟩
      simp [ha, hs, hp, massert, UScalar.val]
    · simp only [WP.spec_ok]

/- Follow the actual built-in associated-constant initializer. This proves
the concrete numerical assertions without assuming a KnownLayout trait law.
-/
theorem u32_slice_known_layout_checks (elems : Usize) :
    layout.primitive_checks.check_u32_slice_known_layout elems ⦃ _ => True ⦄ := by
  classical
  let size : Usize := if U32 = Usize then
    { bv := BitVec.ofNat _ (System.Platform.numBits / 8) } else RustLayout.size U32
  let align := RustLayout.align U32
  have hs : core.mem.size_of U32 = .ok size := rfl
  have ha : core.mem.align_of U32 = .ok align := rfl
  unfold layout.primitive_checks.check_u32_slice_known_layout
  rw [hs, ha]
  simp only [bind_ok]
  step as ⟨enabled, he⟩
  split
  · rename_i yes
    have power : align.val.isPowerOfTwo := Eq.mp he yes
    have positive := Nat.pos_of_isPowerOfTwo power
    step with Usize.rem_spec size (y := align) (by omega) as ⟨remainder, hr⟩
    simp only [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
    split
    · simp only [WP.spec_ok]
    · rename_i divisible
      have remainder_zero : remainder = 0#usize := by
        simpa only [bne_iff_ne, not_not] using divisible
      have multiple : size.val % align.val = 0 := by
        change remainder.val = size.val % align.val at hr
        rw [remainder_zero] at hr
        simpa only [UScalar.ofNatCore_val_eq] using hr.symm
      unfold Slice.Insts.ZerocopyKnownLayout.LAYOUT
      step with for_slice_spec U32 size align hs ha power as
        ⟨slice, hsa, hsp, tail, hsi, ho, hel, hb, hc⟩
      simp [core.num.nonzero.NonZero.get, hsa, hsp, hsi, ho, hel, hb,
        align, size, massert]
      have same : tail.size_rounding_align_and_phase._0.val = align :=
        UScalar.eq_of_val_eq hc
      simp [same, align]
      have encoded_positive : 0 < tail.size_rounding_align_and_phase._0.val.val := by
        rw [same]
        exact positive
      have formula := TailChecks.witness_view tail ⟨align⟩ 0#usize power
        (by simpa using positive) (by simpa using hc)
      step with size_for_elems_spec tail elems encoded_positive as ⟨actual, actual_value⟩
      have product_aligned : (elems.val * size.val) % align.val = 0 := by
        simp [Nat.mul_mod, multiple]
      have size_formula : (trailingFormula tail).size elems.val = elems.val * size.val := by
        rw [formula]
        simp only [TailChecks.witnessFormula, LayoutMath.Formula.size,
          LayoutMath.Formula.bytes, hb, hel, UScalar.ofNatCore_val_eq,
          Nat.zero_add]
        change LayoutMath.roundUp (elems.val * size.val) align.val = elems.val * size.val
        exact LayoutMath.roundUp_eq _ _ product_aligned
      have actual_expected : actual = Usize.checked_mul elems size :=
        TailChecks.optional_value_injective (by
          simp only [LayoutMath.Formula.checkedSize, size_formula] at actual_value
          simpa only [TailChecks.checkedNat] using
            actual_value.trans (TailChecks.checked_mul_value elems size).symm)
      simp only [lift, bind_ok]
      step with TailChecks.same_optional_usize actual (Usize.checked_mul elems size) as
        ⟨same_result, result_iff⟩
      have same_true := result_iff.mpr actual_expected
      simp only [same_true, if_true, WP.spec_ok]
  · simp only [WP.spec_ok]

end Zerocopy.Proofs.Raw

namespace Zerocopy.Proofs

theorem primitive_layout_checks_spec : Specs.primitive_layout_checks_spec := by
  intro T _
  apply WP.spec_mono (Raw.primitive_layout_checks T)
  intro _ _
  exact ⟨(), rfl, trivial⟩

theorem empty_layout_checks_spec : Specs.empty_layout_checks_spec := by
  intro repr_align _ _
  apply WP.spec_mono (Raw.empty_layout_checks repr_align)
  intro _ _
  exact ⟨(), rfl, trivial⟩

theorem u32_slice_known_layout_checks_spec : Specs.u32_slice_known_layout_checks_spec := by
  intro elems _ _
  apply WP.spec_mono (Raw.u32_slice_known_layout_checks elems)
  intro _ _
  exact ⟨(), rfl, trivial⟩

end Zerocopy.Proofs
