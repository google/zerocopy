/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutModel
public import Mathlib.Tactic.NormNum
@[expose] public section
open Aeneas Aeneas.Std Zerocopy Zerocopy.Proofs

namespace Zerocopy.LayoutModelDomainTests

private theorem two_fields_fit : 2 ≤ Usize.max := by
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, h] <;> decide

private theorem one_alignment : alignmentDomain 1 := ⟨Nat.isPowerOfTwo_one, by decide⟩
private theorem two_alignment : alignmentDomain 2 := ⟨by simpa using Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo Nat.isPowerOfTwo_one, by decide⟩
private theorem four_alignment : alignmentDomain 4 := ⟨by simpa using Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo two_alignment.1, by decide⟩

def byteField : layout.DstLayout :=
  { align := ⟨1#usize⟩, size_info := .Sized 1#usize,
    statically_shallow_unpadded := true }

def wordField : layout.DstLayout :=
  { align := ⟨4#usize⟩, size_info := .Sized 4#usize,
    statically_shallow_unpadded := true }

def ordinaryFields : Slice layout.DstLayout :=
  Slice.from [byteField, wordField] (by simpa only [List.length_cons, List.length_nil] using two_fields_fit)

-- The inner aligned DST has physical offset5 but normalized base4/phase1.
def innerAlignedTail : layout.TrailingSliceLayout Usize :=
  { offset := 5#usize, elem_size := 1#usize, size_base := 4#usize,
    size_rounding_align_and_phase := ⟨⟨5#usize⟩⟩ }

def innerAlignedField : layout.DstLayout :=
  { align := ⟨4#usize⟩, size_info := .SliceDst innerAlignedTail,
    statically_shallow_unpadded := true }

def twoBytePrefix : layout.DstLayout :=
  { align := ⟨1#usize⟩, size_info := .Sized 2#usize,
    statically_shallow_unpadded := true }

def packedFields : Slice layout.DstLayout :=
  Slice.from [twoBytePrefix, innerAlignedField]
    (by simpa only [List.length_cons, List.length_nil] using two_fields_fit)

def packedTwo : Option NonZeroUsize := some ⟨2#usize⟩

def nestedDescription : LayoutMath.Description :=
  .record 2 0 (some 1) (.record 5 2 none (.slice 1 0))

-- These explicitly positive examples make False-strengthened domains fail.
theorem ordinary_record_admitted :
    constructionDomain ordinaryFields (LayoutMath.LayoutValue.initial 1) none ∧
    alignmentDomain (constructionPrefix ordinaryFields (LayoutMath.LayoutValue.initial 1) none 2).align ∧
    (constructionPrefix ordinaryFields (LayoutMath.LayoutValue.initial 1) none 2).padFits Usize.max := by
  constructor
  · intro i hi
    have hicases : i = 0 ∨ i = 1 := by
      simp only [ordinaryFields, Slice.from_val, List.length_cons, List.length_nil] at hi
      omega
    rcases hicases with rfl | rfl
    all_goals
      rcases System.Platform.numBits_eq with h | h <;>
        norm_num [constructionPrefix, ordinaryFields, Slice.from_val,
          LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
          LayoutMath.LayoutValue.extend, LayoutMath.LayoutValue.extendFits,
          LayoutMath.roundUp, layoutValue, byteField, wordField, canonicalLayout,
          packingValue, one_alignment, four_alignment, h,
          Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
  · constructor
    · rcases System.Platform.numBits_eq with h | h <;>
        norm_num [constructionPrefix, ordinaryFields, Slice.from_val,
          LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
          LayoutMath.LayoutValue.extend, LayoutMath.roundUp, layoutValue,
          byteField, wordField, packingValue, four_alignment, h]
    · rcases System.Platform.numBits_eq with h | h <;>
        norm_num [constructionPrefix, ordinaryFields, Slice.from_val,
          LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
          LayoutMath.LayoutValue.extend, LayoutMath.LayoutValue.padFits,
          LayoutMath.roundUp, layoutValue, byteField, wordField, packingValue,
          Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, h]

theorem nested_packed_record_admitted :
    (∀ a ∈ packedTwo, alignmentDomain a.val.val) ∧
    constructionDomain packedFields (LayoutMath.LayoutValue.initial 1) packedTwo ∧
    alignmentDomain (constructionPrefix packedFields (LayoutMath.LayoutValue.initial 1) packedTwo 2).align ∧
    (constructionPrefix packedFields (LayoutMath.LayoutValue.initial 1) packedTwo 2).padFits Usize.max := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [packedTwo, two_alignment]
  · intro i hi
    have hicases : i = 0 ∨ i = 1 := by
      simp only [packedFields, Slice.from_val, List.length_cons, List.length_nil] at hi
      omega
    rcases hicases with rfl | rfl
    all_goals
      rcases System.Platform.numBits_eq with h | h <;>
        norm_num [constructionPrefix, packedFields, Slice.from_val,
          LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
          LayoutMath.LayoutValue.extend, LayoutMath.LayoutValue.extendFits,
          LayoutMath.roundUp, layoutValue, twoBytePrefix, innerAlignedField,
          innerAlignedTail, trailingFormula, byteFormula, canonicalLayout,
          packedTwo, packingValue, one_alignment, four_alignment, h,
          Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq,
          show Nat.log2 5 = 2 by decide]
  · norm_num [constructionPrefix, packedFields, Slice.from_val,
      LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
      LayoutMath.LayoutValue.extend, LayoutMath.roundUp, layoutValue,
      twoBytePrefix, innerAlignedField, innerAlignedTail, packedTwo, packingValue,
      trailingFormula, byteFormula, two_alignment, show Nat.log2 5 = 2 by decide]
  · rcases System.Platform.numBits_eq with h | h <;>
      norm_num [constructionPrefix, packedFields, Slice.from_val,
        LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
        LayoutMath.LayoutValue.extend, LayoutMath.LayoutValue.padFits,
        LayoutMath.roundUp, layoutValue, twoBytePrefix, innerAlignedField,
        innerAlignedTail, packedTwo, packingValue, trailingFormula, byteFormula,
        Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, h,
        show Nat.log2 5 = 2 by decide]

-- Exact values distinguish this view from a constant or flattened interpretation.
theorem input_views_are_exact :
    layoutValue byteField = ⟨1, .fixed 1, true⟩ ∧
    layoutValue wordField = ⟨4, .fixed 4, true⟩ ∧
    layoutValue innerAlignedField = ⟨4, .trailing ⟨4, 1, 4, 1, 5⟩, true⟩ := by
  norm_num [layoutValue, byteField, wordField, innerAlignedField, innerAlignedTail,
    trailingFormula, byteFormula, show Nat.log2 5 = 2 by decide]

theorem ordinary_prefix_is_exact :
    (constructionPrefix ordinaryFields (LayoutMath.LayoutValue.initial 1) none 2).pad =
      ⟨4, .fixed 8, false⟩ := by
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [constructionPrefix, ordinaryFields, Slice.from_val,
      LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
      LayoutMath.LayoutValue.extend, LayoutMath.LayoutValue.pad, LayoutMath.roundUp,
      layoutValue, byteField, wordField, packingValue, h]

theorem nested_description_is_valid : nestedDescription.valid := by
  simp [nestedDescription, LayoutMath.Description.valid]

theorem nested_packed_prefix_is_exact :
    (constructionPrefix packedFields (LayoutMath.LayoutValue.initial 1) packedTwo 2).pad =
      ⟨2, .trailing ⟨6, 1, 4, 1, 7⟩, true⟩ := by
  norm_num [constructionPrefix, packedFields, Slice.from_val,
    LayoutMath.LayoutValue.prefixValue, LayoutMath.LayoutValue.initial,
    LayoutMath.LayoutValue.extend, LayoutMath.LayoutValue.pad,
    LayoutMath.Formula.pad, LayoutMath.roundUp, layoutValue, twoBytePrefix,
    innerAlignedField, innerAlignedTail, packedTwo, packingValue, trailingFormula,
    byteFormula, show Nat.log2 5 = 2 by decide]

theorem nested_packed_zero_retains_inner_padding :
    (constructionPrefix packedFields (LayoutMath.LayoutValue.initial 1) packedTwo 2).pad.size 0 = 10 ∧
    nestedDescription.size 0 = 10 ∧ LayoutMath.roundUp 7 2 = 8 := by
  rw [nested_packed_prefix_is_exact]
  norm_num [LayoutMath.LayoutValue.size, LayoutMath.Formula.size,
    LayoutMath.Formula.bytes, LayoutMath.roundUp, nestedDescription,
    LayoutMath.Description.size, LayoutMath.Description.alignExponent,
    LayoutMath.Description.fieldAlignExponent]

-- Representation domains are checked independently of the mathematical view.
theorem nominal_domains_are_admitted :
    layoutValid byteField ∧ layoutValid wordField ∧ layoutValid innerAlignedField := by
  norm_num [layoutValid, sizeInfoValid, trailingValid, encodingValid,
    scalar_valid_iff, byteField, wordField, innerAlignedField, innerAlignedTail]

theorem zero_encoding_is_excluded :
    ¬ encodingValid ⟨⟨0#usize⟩⟩ := by
  norm_num [encodingValid]

end Zerocopy.LayoutModelDomainTests
