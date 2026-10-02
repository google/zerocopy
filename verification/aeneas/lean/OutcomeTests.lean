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

namespace Zerocopy.OutcomeTests

-- Numerical boundary cases independently pin the inline outcome predicates.
def fixedEight : layout.DstLayout :=
  { align := ⟨4#usize⟩, size_info := .Sized 8#usize,
    statically_shallow_unpadded := false }

def plateauTail : layout.TrailingSliceLayout Usize :=
  { offset := 0#usize, elem_size := 1#usize, size_base := 0#usize,
    size_rounding_align_and_phase := ⟨⟨4#usize⟩⟩ }

def plateauFour : layout.DstLayout :=
  { align := ⟨4#usize⟩, size_info := .SliceDst plateauTail,
    statically_shallow_unpadded := true }

def zeroStride : layout.DstLayout :=
  { plateauFour with size_info := .SliceDst { plateauTail with elem_size := 0#usize } }

-- Incorrect Sized metadata is excluded even when the size and split fit.
theorem rejects_wrong_sized_elems :
    ¬ castSpec fixedEight 0 20 .Prefix (.Ok (1#usize, 8#usize)) := by
  norm_num [castSpec, fixedEight, castSide, castSplit]

-- Prefix and suffix splits differ when length is larger than twice the size.
theorem rejects_wrong_prefix_split :
    ¬ castSpec fixedEight 0 20 .Prefix (.Ok (0#usize, 12#usize)) := by
  norm_num [castSpec, fixedEight, castSide, castSplit]

theorem rejects_wrong_suffix_split :
    ¬ castSpec fixedEight 0 20 .Suffix (.Ok (0#usize, 8#usize)) := by
  norm_num [castSpec, fixedEight, castSide, castSplit]

theorem admits_correct_suffix_split :
    castSpec fixedEight 0 20 .Suffix (.Ok (0#usize, 12#usize)) := by
  norm_num [castSpec, fixedEight, castSide, castSplit]

-- Misalignment has priority over insufficient size.
theorem rejects_wrong_error_priority :
    ¬ castSpec fixedEight 1 0 .Prefix (.Err .Size) := by
  norm_num [castSpec, fixedEight, castSide]

theorem admits_alignment_before_size :
    castSpec fixedEight 1 0 .Prefix (.Err .Alignment) := by
  norm_num [castSpec, fixedEight, castSide]

-- A suffix uses the end address: 1+3 is aligned even though 1 is not.
theorem rejects_wrong_suffix_anchor :
    ¬ castSpec fixedEight 1 3 .Suffix (.Err .Alignment) := by
  norm_num [castSpec, fixedEight, castSide]

theorem admits_suffix_size_error :
    castSpec fixedEight 1 3 .Suffix (.Err .Size) := by
  norm_num [castSpec, fixedEight, castSide]

-- One element fits at length 4, but metadata must be the greatest fitting 4.
theorem rejects_nonmaximal_cast_metadata :
    ¬ castSpec plateauFour 0 4 .Prefix (.Ok (1#usize, 4#usize)) := by
  intro h
  have hmaximum := h.2.2.1 4
  norm_num [trailingFormula, byteFormula, plateauFour, plateauTail,
    LayoutMath.Formula.size, LayoutMath.Formula.bytes, LayoutMath.roundUp,
    show Nat.log2 4 = 2 by decide] at hmaximum


theorem rejects_fixed_metadata :
    ¬ metadataSpec fixedEight 8 (some 1#usize) := by
  simp [metadataSpec, fixedEight]

theorem admits_no_fixed_metadata : metadataSpec fixedEight 8 none := by
  simp [metadataSpec, fixedEight]

theorem rejects_zero_stride_metadata :
    ¬ metadataSpec zeroStride 4 (some 1#usize) := by
  simp [metadataSpec, zeroStride, plateauFour, plateauTail]

-- Returning none is incorrect when n=4 has exact complete size 4.
theorem rejects_absent_exact_metadata :
    ¬ metadataSpec plateauFour 4 none := by
  intro h
  have hmissing := h 4
  norm_num [trailingFormula, byteFormula, plateauFour, plateauTail,
    LayoutMath.Formula.size, LayoutMath.Formula.bytes, LayoutMath.roundUp,
    show Nat.log2 4 = 2 by decide] at hmissing

-- Exact complete size alone does not suffice on a padded-size plateau.
theorem rejects_nonmaximal_exact_metadata :
    ¬ metadataSpec plateauFour 4 (some 1#usize) := by
  intro h
  have hmaximum := h.2 4
  norm_num [trailingFormula, byteFormula, plateauFour, plateauTail,
    LayoutMath.Formula.size, LayoutMath.Formula.bytes, LayoutMath.roundUp,
    show Nat.log2 4 = 2 by decide] at hmaximum

theorem rejects_inexact_metadata :
    ¬ metadataSpec plateauFour 3 (some 3#usize) := by
  intro h
  have hexact := h.1
  norm_num [trailingFormula, byteFormula, plateauFour, plateauTail,
    LayoutMath.Formula.size, LayoutMath.Formula.bytes, LayoutMath.roundUp,
    show Nat.log2 4 = 2 by decide] at hexact

end Zerocopy.OutcomeTests
