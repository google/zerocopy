import Toy.Layout.Core
import Toy.Layout.Struct
import Toy.Layout.Enum
import Toy.Layout.Dst

namespace Toy.Layout

/-!
# Execution Cross-Check Against Pinned `rustc`

Each theorem below checks by kernel reduction (`rfl` / `decide`) that the `Toy.Layout`
model reproduces the exact `(size, align, offsets)` recorded from `support/crosscheck.rs`
and `support/crosscheck_short_enum.rs` under
`rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65, 2026-05-31)`:

* 25 concrete types executed on `x86_64-unknown-linux-gnu` (`support/crosscheck_output.txt`),
  including `FieldlessCBigDiscr` (`0x1_0000_0000`) and `DstUnalignedOff<[[u8; 2]]>`;
* 3 short-enum types compile-time checked on `thumbv7m-none-eabi` and
  `hexagon-unknown-none-elf` (`support/crosscheck_short_enum_output.txt`).

**Evidence boundary:** The Lean kernel checks only the model's numbers; the `rustc`
numbers are transcribed from the recorded program outputs. These equalities are empirical
corroboration of the modeling bridge on concrete types, not a proof of equivalence with
`rustc` for all types or targets.
-/

theorem xc_01_empty :
    reprCStruct .none [] = { offsets := [], endOffset := 0, size := 0, align := 1 } := rfl

theorem xc_02_asc_pad :
    reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩, ⟨2, 2⟩] =
      { offsets := [0, 4, 8], endOffset := 10, size := 12, align := 4 } := rfl

theorem xc_03_three_ints :
    reprCStruct .none [⟨2, 2⟩, ⟨1, 1⟩, ⟨4, 4⟩] =
      { offsets := [0, 2, 4], endOffset := 8, size := 8, align := 4 } := rfl

theorem xc_04_trail_pad :
    reprCStruct .none [⟨2, 2⟩, ⟨1, 1⟩] =
      { offsets := [0, 2], endOffset := 3, size := 4, align := 2 } := rfl

theorem xc_05_u8_u16 :
    reprCStruct .none [⟨1, 1⟩, ⟨2, 2⟩] =
      { offsets := [0, 2], endOffset := 4, size := 4, align := 2 } := rfl

theorem xc_06_zst_mid :
    reprCStruct .none [⟨1, 1⟩, ⟨0, 4⟩, ⟨1, 1⟩] =
      { offsets := [0, 4, 4], endOffset := 5, size := 8, align := 4 } := rfl

theorem xc_07_homog :
    reprCStruct .none [⟨4, 4⟩, ⟨4, 4⟩, ⟨4, 4⟩] =
      { offsets := [0, 4, 8], endOffset := 12, size := 12, align := 4 } := rfl

theorem xc_08_packed1 :
    reprCStruct (.packed 1) [⟨1, 1⟩, ⟨4, 4⟩, ⟨2, 2⟩] =
      { offsets := [0, 1, 5], endOffset := 7, size := 7, align := 1 } := rfl

theorem xc_09_packed2 :
    reprCStruct (.packed 2) [⟨1, 1⟩, ⟨4, 4⟩, ⟨1, 1⟩] =
      { offsets := [0, 2, 6], endOffset := 7, size := 8, align := 2 } := rfl

theorem xc_10_packed_noop :
    reprCStruct (.packed 8) [⟨1, 1⟩, ⟨4, 4⟩, ⟨2, 2⟩] =
      { offsets := [0, 4, 8], endOffset := 10, size := 12, align := 4 } := rfl

theorem xc_11_aligned8 :
    reprCStruct (.aligned 8) [⟨2, 2⟩, ⟨1, 1⟩] =
      { offsets := [0, 2], endOffset := 3, size := 8, align := 8 } := rfl

theorem xc_12_aligned_noop :
    reprCStruct (.aligned 2) [⟨1, 1⟩, ⟨4, 4⟩, ⟨2, 2⟩] =
      { offsets := [0, 4, 8], endOffset := 10, size := 12, align := 4 } := rfl

theorem xc_13_size_rounded_up_union :
    reprCUnion [⟨4, 4⟩, ⟨6, 2⟩] = { size := 8, align := 4 } := rfl

theorem xc_14_fieldless_c_enum :
    reprCEnumForTarget targetX86_64Linux 0 1 [[], []] =
      { size := 4, align := 4, tagOffset := 0, variantFieldOffsets := [[], []] } := rfl

theorem xc_14b_fieldless_c_enum_big_discr :
    reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 [[], []] =
      { size := 8, align := 8, tagOffset := 0, variantFieldOffsets := [[], []] } := rfl

theorem xc_15_enum_c :
    reprCEnumForTarget targetX86_64Linux 0 1 [[⟨1, 1⟩], []] =
      { size := 8, align := 4, tagOffset := 0, variantFieldOffsets := [[4], []] } := rfl

theorem xc_16_ref_enum :
    reprCEnumForTarget targetX86_64Linux 0 3 [[⟨4, 4⟩], [⟨4, 4⟩, ⟨8, 8⟩], [⟨4, 4⟩, ⟨1, 1⟩], []] =
      { size := 24, align := 8, tagOffset := 0,
        variantFieldOffsets := [[8], [8, 16], [8, 12], []] } := rfl

theorem xc_17a_enum_c_u8 :
    reprCEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []] =
      { size := 6, align := 2, tagOffset := 0, variantFieldOffsets := [[2, 4], []] } := rfl

theorem xc_17b_enum_u8 :
    reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []] =
      { size := 4, align := 2, tagOffset := 0, variantFieldOffsets := [[1, 2], []] } := rfl

theorem xc_18a_dst_trail_pad :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩
    dstTailOffset d = 4 ∧ dstAlign d = 4 ∧
    [0, 1, 2, 3, 4, 5].map (dstSize d) = [4, 8, 8, 8, 8, 12] := by
  decide

theorem xc_18b_dst_unaligned_off :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    dstTailOffset d = 3 ∧ dstAlign d = 2 ∧
    [0, 1, 2, 3, 4, 5].map (dstSize d) = [4, 4, 6, 6, 8, 8] := by
  decide

theorem xc_18c_dst_packed1 :
    let d : SliceDstSpec := ⟨.packed 1, [⟨4, 4⟩], ⟨1, 1⟩⟩
    dstTailOffset d = 4 ∧ dstAlign d = 1 ∧
    [0, 1, 2, 3].map (dstSize d) = [4, 5, 6, 7] := by
  decide

theorem xc_18d_dst_packed2 :
    let d : SliceDstSpec := ⟨.packed 2, [⟨1, 1⟩], ⟨4, 4⟩⟩
    dstTailOffset d = 2 ∧ dstAlign d = 2 ∧
    [0, 1, 2, 3].map (dstSize d) = [2, 6, 10, 14] := by
  decide

theorem xc_18e_dst_align4_elem3 :
    let d : SliceDstSpec := ⟨.aligned 4, [⟨1, 1⟩], ⟨3, 1⟩⟩
    dstTailOffset d = 1 ∧ dstAlign d = 4 ∧
    [0, 1, 2, 3, 4].map (dstSize d) = [4, 4, 8, 12, 16] := by
  decide

theorem xc_18f_dst_unaligned_off_elem2 :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩
    dstTailOffset d = 3 ∧ dstAlign d = 2 ∧
    [0, 1, 2, 3].map (dstSize d) = [4, 6, 8, 10] := by
  decide

theorem xc_19_thumb_short_enums :
    reprCEnumForTarget targetThumbV7mNoneEabi 0 1 [[], []] =
      { size := 1, align := 1, tagOffset := 0, variantFieldOffsets := [[], []] } ∧
    reprCEnumForTarget targetThumbV7mNoneEabi 256 257 [[], []] =
      { size := 2, align := 2, tagOffset := 0, variantFieldOffsets := [[], []] } ∧
    reprCEnumForTarget targetThumbV7mNoneEabi 0 1 [[⟨1, 1⟩], []] =
      { size := 2, align := 1, tagOffset := 0, variantFieldOffsets := [[1], []] } := by
  decide

theorem xc_20_hexagon_short_enums :
    reprCEnumForTarget targetHexagonNoneElf 0 1 [[], []] =
      { size := 1, align := 1, tagOffset := 0, variantFieldOffsets := [[], []] } ∧
    reprCEnumForTarget targetHexagonNoneElf 256 257 [[], []] =
      { size := 2, align := 2, tagOffset := 0, variantFieldOffsets := [[], []] } ∧
    reprCEnumForTarget targetHexagonNoneElf 0 1 [[⟨1, 1⟩], []] =
      { size := 2, align := 1, tagOffset := 0, variantFieldOffsets := [[1], []] } := by
  decide

end Toy.Layout
