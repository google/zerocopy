/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import LayoutMath
@[expose] public section

namespace Zerocopy.SplitMath
open LayoutMath

/-- Half-open byte ranges [0, leftSize) and [rightStart, rightStart + rightBytes).
This definition includes empty ranges and contains no pointer assumptions. -/
def Disjoint (leftSize rightStart rightBytes : Nat) : Prop :=
  ∀ byte, ¬ (byte < leftSize ∧ rightStart ≤ byte ∧ byte < rightStart + rightBytes)

theorem disjoint_of_boundary (leftSize rightStart rightBytes : Nat)
    (boundary : leftSize ≤ rightStart) : Disjoint leftSize rightStart rightBytes := by
  intro byte overlap
  omega

theorem empty_right_disjoint (leftSize rightStart : Nat) :
    Disjoint leftSize rightStart 0 := by
  intro byte overlap
  omega

/-- Every count, product, sum and output length fits in the original byte
budget. The physical-tail premise is explicit because arbitrary Formula
records need not describe a realizable Rust layout. -/
theorem split_bounds (f : Formula) (total left limit : Nat)
    (positive : 0 < f.align) (index : left ≤ total)
    (contains : f.offset + total * f.elem ≤ f.size total)
    (fits : f.size total ≤ limit) :
    (total - left) + left = total ∧ total - left ≤ total ∧
    f.size left ≤ f.size total ∧ f.size left ≤ limit ∧
    left * f.elem ≤ limit ∧ (total - left) * f.elem ≤ limit ∧
    f.offset + left * f.elem ≤ limit ∧
    f.offset + left * f.elem + (total - left) * f.elem =
      f.offset + total * f.elem ∧
    f.offset + left * f.elem + (total - left) * f.elem ≤ f.size total := by
  have counts : (total - left) + left = total := by omega
  have mono := f.size_mono positive index
  have leftBytes := Nat.mul_le_mul_right f.elem index
  have rightBytes := Nat.mul_le_mul_right f.elem (show total - left ≤ total by omega)
  have sumBytes : left * f.elem + (total - left) * f.elem = total * f.elem := by
    rw [← Nat.add_mul, Nat.add_comm left, counts]
  exact ⟨counts, by omega, mono, by omega, by omega, by omega,
    by omega, by omega, by omega⟩

/-- Zero padding yields the shared boundary and therefore disjointness.
This is a sufficient condition, never asserted to be necessary. -/
theorem runtime_disjoint (f : Formula) (total left : Nat)
    (zero : f.size left = f.offset + left * f.elem) :
    Disjoint (f.size left) (f.offset + left * f.elem) ((total - left) * f.elem) := by
  apply disjoint_of_boundary
  omega

theorem static_disjoint (f : Formula) (total left : Nat)
    (initial : f.size 0 = f.offset) (stride : f.elem % f.align = 0) :
    Disjoint (f.size left) (f.offset + left * f.elem) ((total - left) * f.elem) :=
  runtime_disjoint f total left (no_dynamic_padding f initial stride left)

/-- The exact recursive layout domain discharges physical containment for all
indices, including arbitrary nested packing and zero-sized elements. -/
theorem compiled_split_bounds (d : Description) (valid : d.valid)
    (total left limit : Nat) (index : left ≤ total)
    (fits : d.compile.size total ≤ limit) :
    (total - left) + left = total ∧ total - left ≤ total ∧
    d.compile.size left ≤ d.compile.size total ∧ d.compile.size left ≤ limit ∧
    left * d.compile.elem ≤ limit ∧ (total - left) * d.compile.elem ≤ limit ∧
    d.compile.offset + left * d.compile.elem ≤ limit ∧
    d.compile.offset + left * d.compile.elem + (total - left) * d.compile.elem =
      d.compile.offset + total * d.compile.elem ∧
    d.compile.offset + left * d.compile.elem + (total - left) * d.compile.elem ≤
      d.compile.size total :=
  split_bounds d.compile total left limit (compile_valid d).1 index
    (compiled_contains_tail d valid total) fits

theorem zst_right_disjoint (f : Formula) (total left : Nat) (zst : f.elem = 0) :
    Disjoint (f.size left) (f.offset + left * f.elem) ((total - left) * f.elem) := by
  rw [zst, Nat.mul_zero]
  exact empty_right_disjoint _ _

theorem end_split_disjoint (f : Formula) (total : Nat) :
    Disjoint (f.size total) (f.offset + total * f.elem) ((total - total) * f.elem) := by
  rw [Nat.sub_self, Nat.zero_mul]
  exact empty_right_disjoint _ _

/-- Explicitly exhibit why zero padding must not be claimed necessary. -/
theorem padded_empty_example : Disjoint 4 1 0 ∧ 4 ≠ 1 :=
  ⟨empty_right_disjoint 4 1, by decide⟩

end Zerocopy.SplitMath
