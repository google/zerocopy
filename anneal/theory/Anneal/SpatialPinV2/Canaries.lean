-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Trusted.MirAst
public import Trusted.MirModel
public import Anneal.SpatialPinV2.Tile
public import Anneal.SpatialPinV2.Stencil

public section

/-!
# SpatialPin v2 Canaries (`Canaries`)

Concrete positive witnesses and negative counterexamples exercising the core
laws in `Anneal.SpatialPinV2`:

1. **Canary 1 (`canary1_codecRegistry_and_pinMode_laws`):**
   - Verifies closure-free `List CodecMeta` unique-ID acceptance and
     unambiguous `lookupCodecMeta_eq_of_mem_unique`, fail-closed rejection of
     duplicate codec IDs, and 3-mode `SpatialPinMode` readability preservation
     + duplicability (`modeDuplicable_iff_readOnly`).
2. **Canary 2 (`canary2_4k_bwdStride_splits_and_naive_col_overlap`):**
   - Splits a 4K-scale (`3840×2160`, `absStride = 4096`) backward-strided
     (`.bwd`) `SymbolicTile2D` horizontally and vertically in $O(1)$
     (`tileSplitRows` / `tileSplitCols`), verifies `TileWellFormed`,
     disjointness, exact coverage, empty-split base guards (`r = height`,
     `c = width`), and `tileInOwned_lt_allocLen`.
   - Proves a concrete negative counterexample where naive column splitting
     without `ownedSpan` shedding aliases row-padding bytes (`[4..16)` overlap,
     concrete witness byte `8` in tail `[8..16)`).
3. **Canary 3 (`canary3_chroma_ceil_and_mbaff_luma6_oob_catch`):**
   - Proves `chromaCeilShift_bounds_last_row` across `4:2:0` (`ss = 1`) and
     `4:4:4` (`ss = 0`), refutes floor-shifting on odd `h = 5`, and proves
     `fieldActiveRows` catches the `lumaH = 6` -> chroma `3` bottom-field OOB
     (`fieldActiveRows 3 true = 1`, `fieldActiveRows 3 false = 2`,
     `∃ y < fieldActiveRows 3 false, ¬ (2 * y + 1 < 3)`).
4. **Canary 4 (`canary4_activeMask_demonic_uninit_and_leaky_refutation`):**
   - Proves `PaddingIndependent` + sequential composition + demonic `.uninit`
     elimination on a concrete masked 4-active / 4-padding SIMD row kernel,
     contrasted with a leaky padding-copy kernel that refutes
     `PaddingIndependent`.
5. **Canary 5 (`canary5_overlapping_stencil_and_causal_sweep`):**
   - Exercises `classifyZone_complete`, `OverlapKernelSound`, frame/read-only
     preservation, and `.writeOnly` `.uninit`-insensitivity on a concrete
     overlapping 8-tap stencil (`R = [2..10)`, `W = [4..8)`), followed by a
     2-step causal wavefront prefix sweep (`causalSweep_sound`) preserving
     untouched frame coordinates.

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.SpatialPinV2

open Trusted.MirAst Trusted.MirSemantics

/-! ## Canary 1: Closure-Free `List CodecMeta` & 3-Mode `SpatialPinMode` -/

/-- Valid 3-entry closure-free `List CodecMeta` with distinct codec IDs. -/
@[expose] def canary1ValidReg : List CodecMeta :=
  [{ codecId := 1, byteLen := 1, alignLog2 := 0, elemSize := 1 },
   { codecId := 2, byteLen := 4, alignLog2 := 2, elemSize := 2 },
   { codecId := 3, byteLen := 16, alignLog2 := 4, elemSize := 4 }]

/-- Duplicate-ID `List CodecMeta` (two entries sharing `codecId = 2`). -/
@[expose] def canary1DupReg : List CodecMeta :=
  [{ codecId := 2, byteLen := 1, alignLog2 := 0, elemSize := 1 },
   { codecId := 2, byteLen := 4, alignLog2 := 2, elemSize := 2 }]

/-- Canary 1 (`[]` zero axioms): exercises `checkRegistryUniqueIds`,
`lookupCodecMeta_eq_of_mem_unique`, duplicate-ID rejection, and 3-mode
`SpatialPinMode` lifecycle + duplicability laws. -/
theorem canary1_codecRegistry_and_pinMode_laws :
    checkRegistryUniqueIds canary1ValidReg = true ∧
    checkRegistryUniqueIds canary1DupReg = false ∧
    lookupCodecMeta canary1ValidReg 2 =
      some { codecId := 2, byteLen := 4, alignLog2 := 2, elemSize := 2 } ∧
    modeCanRead .readOnly = true ∧
    modeDuplicable .readOnly = true ∧
    modeDuplicable .readWrite = false ∧
    modeDuplicable .uninit = false := by
  have hUniq : checkRegistryUniqueIds canary1ValidReg = true := rfl
  have hMem :
      { codecId := 2, byteLen := 4, alignLog2 := 2, elemSize := 2 } ∈
        canary1ValidReg :=
    List.Mem.tail _ (List.Mem.head _)
  have hReadFrozen : modeCanRead .readOnly = true :=
    modeStep_preserves_canRead (Or.inr (Or.inr ⟨rfl, rfl⟩)) rfl
  exact ⟨hUniq, rfl, lookupCodecMeta_eq_of_mem_unique hUniq hMem,
    hReadFrozen, (modeDuplicable_iff_readOnly .readOnly).mpr rfl, rfl, rfl⟩

/-! ## Canary 2: 4K Negative-Stride `SymbolicTile2D` & Naive Overlap Catch -/

/-- 4K-scale bottom-up (`.bwd`) negative-stride luma plane (`3840×2160`,
`ownedSpan = 3904`, `absStride = 4096`, `base = 2159 * 4096 = 8_843_264`). -/
@[expose] def canary2Tile4kBwd : SymbolicTile2D :=
  { allocId := 3
    base := 2159 * 4096
    width := 3840
    height := 2160
    elemSize := 1
    ownedSpan := 3904
    absStride := 4096
    dir := .bwd }

/-- Small padded 2D tile (`width = 8`, `elemSize = 1`, `ownedSpan = 16`,
`absStride = 16`) demonstrating why naive column splitting without `ownedSpan`
shedding overlaps on `[4..16)` (witnessed at byte `8` in tail `[8..16)`). -/
@[expose] def canary2SmallPadded : SymbolicTile2D :=
  { allocId := 1
    base := 0
    width := 8
    height := 2
    elemSize := 1
    ownedSpan := 16
    absStride := 16
    dir := .fwd }

/-- Buggy naive column split that forgets to shed `ownedSpan` on the left half
(keeping `ownedSpan = t.ownedSpan`), aliasing `[4..16)` with the right half. -/
@[expose] def naiveBadSplitCols (t : SymbolicTile2D) (c : Nat) :
    SymbolicTile2D × SymbolicTile2D :=
  ({ t with width := c },
   { t with base := t.base + c * t.elemSize,
            width := t.width - c,
            ownedSpan := t.ownedSpan - c * t.elemSize })

private theorem canary2_le1 : 3840 * 1 ≤ 3904 := Nat.le_of_ble_eq_true rfl
private theorem canary2_le2 : 3904 ≤ 4096 := Nat.le_of_ble_eq_true rfl
private theorem canary2_leRow : 1080 ≤ 2160 := Nat.le_of_ble_eq_true rfl
private theorem canary2_leCol : 1920 ≤ 3840 := Nat.le_of_ble_eq_true rfl

/-- Canary 2 (`[propext]` only): verifies $O(1)$ well-formedness,
disjointness, exact coverage, empty-split base guards (`r = 2160` and tight
`c = 3840`), and allocation bounds on a 4K bottom-up `.bwd` tile, plus a
concrete overlap witness refuting `naiveBadSplitCols` without `ownedSpan`
shedding. -/
theorem canary2_4k_bwdStride_splits_and_naive_col_overlap :
    let spR := tileSplitRows canary2Tile4kBwd 1080
    let spC := tileSplitCols spR.1 1920
    TileWellFormed spR.1 ∧
    TileWellFormed spR.2 ∧
    TileWellFormed spC.1 ∧
    TileWellFormed spC.2 ∧
    (∀ aid off, TileInOwned spR.1 aid off → ¬ TileInOwned spR.2 aid off) ∧
    (∀ aid off, TileInOwned spC.1 aid off → ¬ TileInOwned spC.2 aid off) ∧
    (tileSplitRows canary2Tile4kBwd 2160).2.base = canary2Tile4kBwd.base ∧
    (tileSplitCols { canary2Tile4kBwd with ownedSpan := 3840 } 3840).2.base =
      canary2Tile4kBwd.base ∧
    (∀ aid off,
      TileInOwned canary2Tile4kBwd aid off ↔
        TileInOwned spR.1 aid off ∨ TileInOwned spR.2 aid off) ∧
    (∀ (alloc : Allocation) (aid : AllocId) (off : Nat),
      canary2Tile4kBwd.allocId = alloc.allocId →
      tileMaxByteBound canary2Tile4kBwd ≤ alloc.bytes.length →
      TileInOwned canary2Tile4kBwd aid off →
      aid = alloc.allocId ∧ off < alloc.bytes.length ∧
        (canary2Tile4kBwd.dir = .bwd →
          (canary2Tile4kBwd.height - 1) * canary2Tile4kBwd.absStride ≤
            canary2Tile4kBwd.base)) ∧
    (TileInOwned (naiveBadSplitCols canary2SmallPadded 4).1 1 8 ∧
      TileInOwned (naiveBadSplitCols canary2SmallPadded 4).2 1 8) := by
  intro spR spC
  have hWf4k : TileWellFormed canary2Tile4kBwd :=
    ⟨canary2_le1, canary2_le2, fun _ _ => Nat.le_refl _⟩
  have hWfR := tileSplitRows_wellFormed hWf4k canary2_leRow
  have hWfC := tileSplitCols_wellFormed hWfR.1 canary2_leCol
  refine ⟨hWfR.1, hWfR.2, hWfC.1, hWfC.2,
    fun _ _ h1 h2 => tileSplitRows_disjoint hWf4k canary2_leRow h1 h2,
    fun _ _ h1 h2 => tileSplitCols_disjoint hWfR.1 canary2_leCol h1 h2,
    rfl, rfl,
    fun aid off => tileSplitRows_covers_iff canary2_leRow aid off,
    fun _ _ _ hAid hBnd hIn => tileInOwned_lt_allocLen hWf4k hAid hBnd hIn,
    ⟨⟨rfl, 0, 8, Nat.zero_lt_succ 1, Nat.le_of_ble_eq_true rfl, rfl⟩,
     ⟨rfl, 0, 4, Nat.zero_lt_succ 1, Nat.le_of_ble_eq_true rfl, rfl⟩⟩⟩

/-! ## Canary 3: Chroma Ceiling-Shift & `MBAFF` `lumaH = 6` OOB Catch -/

/-- Canary 3 (`[propext]` only): proves `chromaCeilShift_bounds_last_row` on
4:2:0 (`h = 5`, `ss = 1`) and 4:4:4 (`h = 5`, `ss = 0`), proves floor-shifting
under-allocates at `h = 5`, and catches the `lumaH = 6` -> 4:2:0 chroma `hC =
3` bottom-field OOB via `fieldActiveRows` + `mbaff_fieldRow_inBounds` +
`mbaff_bottom_ceil_oob_odd`. -/
theorem canary3_chroma_ceil_and_mbaff_luma6_oob_catch :
    Nat.div (5 - 1) (Nat.pow 2 1) < chromaCeilShift 5 1 ∧
    Nat.div (5 - 1) (Nat.pow 2 0) < chromaCeilShift 5 0 ∧
    ¬ (Nat.div (5 - 1) 2 < Nat.div 5 2) ∧
    chromaCeilShift 6 1 = 3 ∧
    fieldActiveRows 3 false + fieldActiveRows 3 true = 3 ∧
    fieldActiveRows 3 true = 1 ∧
    fieldActiveRows 3 false = 2 ∧
    (∀ y, y < fieldActiveRows 3 true → 2 * y + 1 < 3) ∧
    (∃ y : Nat, y < fieldActiveRows 3 false ∧ ¬ (2 * y + 1 < 3)) := by
  have hOdd5 := chromaFloorShift_underallocates_odd 2
  have hMbaff3 := mbaff_bottom_ceil_oob_odd 1
  exact ⟨chromaCeilShift_bounds_last_row (Nat.zero_lt_succ 4) (Nat.le_refl 1),
    chromaCeilShift_bounds_last_row (Nat.zero_lt_succ 4) (Nat.zero_le 1),
    hOdd5.2,
    rfl,
    fieldActiveRows_sum 3,
    hMbaff3.1,
    hMbaff3.2.1,
    fun y hy => (mbaff_fieldRow_inBounds 3 y).2 hy,
    hMbaff3.2.2⟩

/-! ## Canary 4: Active-Mask Demonic `Uninit`-Padding Independence -/

/-- Active mask selecting the 4 active payload lanes `[0..4)` out of an 8-byte
SIMD row whose tail `[4..8)` may hold `.uninit` padding. -/
@[expose] def canary4Active4 (i : Nat) : Bool :=
  Nat.blt i 4

/-- Padding-independent byte-increment kernel operating strictly inside
`[0..4)`. -/
@[expose] def canary4SafeKernel (m : Nat → AllocByte) : Nat → AllocByte :=
  fun i =>
    if canary4Active4 i then
      match m i with
      | .init b p => .init (UInt8.ofNat (b.toNat + 1)) p
      | .uninit => .uninit
    else
      .uninit

/-- Leaky kernel that reads padding lane `4` when computing active lane `0`,
violating `PaddingIndependent`. -/
@[expose] def canary4LeakyKernel (m : Nat → AllocByte) : Nat → AllocByte :=
  fun i =>
    if Nat.beq i 0 then m 4 else m i

/-- Canary 4 (`[]` zero axioms): proves `PaddingIndependent` for
`canary4SafeKernel`, sequential composition (`paddingIndependent_comp`), and
demonic `.uninit`-tail invariance (`paddingIndependent_demonic_uninit_free`),
while refuting `PaddingIndependent` for `canary4LeakyKernel`. -/
theorem canary4_activeMask_demonic_uninit_and_leaky_refutation :
    PaddingIndependent canary4Active4 canary4Active4 canary4SafeKernel ∧
    PaddingIndependent canary4Active4 canary4Active4
      (fun m => canary4SafeKernel (canary4SafeKernel m)) ∧
    (∀ spec padEnv,
      AgreeOnActive canary4Active4
        (canary4SafeKernel (withDemonicPadding canary4Active4 spec padEnv))
        (canary4SafeKernel spec)) ∧
    ¬ PaddingIndependent canary4Active4 canary4Active4 canary4LeakyKernel := by
  have hSafe :
      PaddingIndependent canary4Active4 canary4Active4 canary4SafeKernel := by
    intro m₁ m₂ hAgree i hi
    dsimp only [canary4SafeKernel]
    rw [hi, hAgree i hi]
  refine ⟨hSafe, paddingIndependent_comp hSafe hSafe,
    fun spec padEnv =>
      paddingIndependent_demonic_uninit_free hSafe spec padEnv, ?_⟩
  intro hLeaky
  let m₁ : Nat → AllocByte := fun i =>
    if Nat.blt i 4 then .init 1 none else .uninit
  let m₂ : Nat → AllocByte := fun i =>
    if Nat.blt i 4 then .init 1 none else .init 9 none
  have hAg : AgreeOnActive canary4Active4 m₁ m₂ := by
    intro i hi
    dsimp only [canary4Active4] at hi
    dsimp only [m₁, m₂]
    rw [hi]
    rfl
  have hOut0 := hLeaky m₁ m₂ hAg 0 rfl
  nomatch hOut0

/-! ## Canary 5: Tri-Partitioned Overlapping Stencil & Causal Wavefront Sweep -/

/-- Overlapping stencil read footprint `[2..10)` (8-tap window). -/
@[expose] def canary5InR (a : Nat) : Bool :=
  Nat.ble 2 a && Nat.blt a 10

/-- Overlapping stencil write footprint `[4..8)` (`W ⊂ R`). -/
@[expose] def canary5InW (a : Nat) : Bool :=
  Nat.ble 4 a && Nat.blt a 8

/-- Pure overlapping stencil updating `[4..8)` from `m a` and `m (a - 2)` (both
inside `R = [2..10)`), preserving all coordinates outside `[4..8)`. -/
@[expose] def canary5StencilKernel (m : Nat → AllocByte) : Nat → AllocByte :=
  fun a =>
    if canary5InW a then
      match m a, m (a - 2) with
      | .init b₁ _, .init b₂ _ =>
        .init (UInt8.ofNat (b₁.toNat + b₂.toNat)) none
      | _, _ => .uninit
    else
      m a

/-- Second causal sweep step reading `[4..8)` and writing fresh `.writeOnly`
block `[8..12)`. -/
@[expose] def canary5Step2InR (a : Nat) : Bool :=
  Nat.ble 4 a && Nat.blt a 8

/-- Write footprint `[8..12)` for causal step 2. -/
@[expose] def canary5Step2InW (a : Nat) : Bool :=
  Nat.ble 8 a && Nat.blt a 12

/-- Pure causal copy step copying `[4..8)` forward into `[8..12)`. -/
@[expose] def canary5Step2Kernel (m : Nat → AllocByte) : Nat → AllocByte :=
  fun a =>
    if canary5Step2InW a then
      match m (a - 4) with
      | .init b _ => .init b none
      | .uninit => .uninit
    else
      m a

private theorem canary5_inR_of_inW {a : Nat} (hW : canary5InW a = true) :
    canary5InR a = true ∧ canary5InR (a - 2) = true := by
  dsimp only [canary5InW] at hW
  dsimp only [canary5InR]
  cases hGe4 : Nat.ble 4 a with
  | false => rw [hGe4] at hW; exact Bool.noConfusion hW
  | true =>
    rw [hGe4] at hW
    have h4 : 4 ≤ a := Nat.le_of_ble_eq_true hGe4
    have hLt8 : a < 8 := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hW)
    have h2Le : 2 ≤ a := Nat.le_trans (Nat.le_of_ble_eq_true rfl) h4
    have hLt10 : a < 10 := Nat.lt_trans hLt8 (Nat.le_of_ble_eq_true rfl)
    have hSubGe2 : 2 ≤ a - 2 := by
      have hSub := Nat.sub_le_sub_right h4 2
      exact hSub
    have hSubLt10 : a - 2 < 10 :=
      Nat.lt_of_le_of_lt (Nat.sub_le a 2) hLt10
    have hBle2 : Nat.ble 2 a = true := Nat.ble_eq_true_of_le h2Le
    have hBlt10 : Nat.blt a 10 = true := Nat.ble_eq_true_of_le hLt10
    have hBleSub2 : Nat.ble 2 (a - 2) = true := Nat.ble_eq_true_of_le hSubGe2
    have hBltSub10 : Nat.blt (a - 2) 10 = true :=
      Nat.ble_eq_true_of_le hSubLt10
    rw [hBle2, hBlt10, hBleSub2, hBltSub10]
    exact ⟨rfl, rfl⟩

private theorem canary5_step2_src_inR {a : Nat}
    (hW : canary5Step2InW a = true) :
    canary5Step2InR (a - 4) = true := by
  dsimp only [canary5Step2InW] at hW
  dsimp only [canary5Step2InR]
  cases hGe8 : Nat.ble 8 a with
  | false => rw [hGe8] at hW; exact Bool.noConfusion hW
  | true =>
    rw [hGe8] at hW
    have h8 : 8 ≤ a := Nat.le_of_ble_eq_true hGe8
    have hLt12 : a < 12 := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hW)
    have hSubGe4 : 4 ≤ a - 4 := Nat.sub_le_sub_right h8 4
    have hSubLt8 : a - 4 < 8 :=
      Nat.sub_lt_sub_right
        (Nat.le_trans (Nat.le_of_ble_eq_true rfl) h8) hLt12
    have hBlt8 : Nat.blt (a - 4) 8 = true := Nat.ble_eq_true_of_le hSubLt8
    rw [Nat.ble_eq_true_of_le hSubGe4, hBlt8]
    rfl

/-- Canary 5 (`[propext]` only): proves four-zone classification on
`canary5InR`/`canary5InW` (`.readOnly`, `.readWrite`, `.frame`) and
`canary5Step2InR`/`canary5Step2InW` (`.writeOnly`), `OverlapKernelSound` for
`canary5StencilKernel` and `canary5Step2Kernel`, read-only / frame preservation,
`.writeOnly` `.uninit`-insensitivity, and 2-step `causalSweep_sound`
initializing `[2..12)` while framing coordinates `0` and `15` untouched. -/
theorem canary5_overlapping_stencil_and_causal_sweep :
    classifyZone canary5InR canary5InW 2 = .readOnly ∧
    classifyZone canary5InR canary5InW 5 = .readWrite ∧
    classifyZone canary5Step2InR canary5Step2InW 9 = .writeOnly ∧
    classifyZone canary5InR canary5InW 15 = .frame ∧
    OverlapKernelSound canary5InR canary5InW canary5StencilKernel ∧
    (∀ m : Nat → AllocByte,
      canary5StencilKernel m 2 = m 2 ∧
      canary5StencilKernel m 15 = m 15) ∧
    (∀ m padEnv : Nat → AllocByte,
      AgreeOnActive canary5Step2InW
        (canary5Step2Kernel (withDemonicPadding canary5Step2InR m padEnv))
        (canary5Step2Kernel m)) ∧
    (∀ m : Nat → AllocByte,
      AllActiveInit canary5InR m →
      let steps : List CausalStep :=
        [⟨canary5InR, canary5InW, canary5StencilKernel⟩,
         ⟨canary5Step2InR, canary5Step2InW, canary5Step2Kernel⟩]
      AllActiveInit (causalPrefixAfter steps canary5InR)
        (runCausalSteps steps m) ∧
      runCausalSteps steps m 0 = m 0 ∧
      runCausalSteps steps m 15 = m 15) := by
  have hS1 : OverlapKernelSound canary5InR canary5InW canary5StencilKernel := by
    refine ⟨?_, ?_, ?_⟩
    · intro m a hNotW
      dsimp only [canary5StencilKernel]
      rw [hNotW]
      rfl
    · intro m₁ m₂ hAg a haW
      have hInR := canary5_inR_of_inW haW
      dsimp only [canary5StencilKernel]
      rw [haW, hAg a hInR.1, hAg (a - 2) hInR.2]
    · intro m hInit a haW
      have hInR := canary5_inR_of_inW haW
      dsimp only [canary5StencilKernel]
      rw [haW]
      cases hInit a hInR.1 with
      | intro b₁ h1 =>
        cases h1 with
        | intro p₁ hp₁ =>
          cases hInit (a - 2) hInR.2 with
          | intro b₂ h2 =>
            cases h2 with
            | intro p₂ hp₂ =>
              rw [hp₁, hp₂]
              exact ⟨UInt8.ofNat (b₁.toNat + b₂.toNat), none, rfl⟩
  have hS2 :
      OverlapKernelSound canary5Step2InR canary5Step2InW
        canary5Step2Kernel := by
    refine ⟨?_, ?_, ?_⟩
    · intro m a hNotW
      dsimp only [canary5Step2Kernel]
      rw [hNotW]
      rfl
    · intro m₁ m₂ hAg a haW
      dsimp only [canary5Step2Kernel]
      rw [haW, hAg (a - 4) (canary5_step2_src_inR haW)]
      rfl
    · intro m hInit a haW
      dsimp only [canary5Step2Kernel]
      rw [haW]
      cases hInit (a - 4) (canary5_step2_src_inR haW) with
      | intro b hb =>
        cases hb with
        | intro p hp =>
          rw [hp]
          exact ⟨b, none, rfl⟩
  refine ⟨rfl, rfl, rfl, rfl, hS1,
    fun m =>
      ⟨overlapKernelSound_preserves_nonWritten hS1 m 2 (Or.inl rfl),
       overlapKernelSound_preserves_nonWritten hS1 m 15 (Or.inr rfl)⟩,
    fun m padEnv =>
      overlapKernelSound_writeOnly_uninit_insensitive hS2 m padEnv,
    fun m hInit => ?_⟩
  let steps : List CausalStep :=
    [⟨canary5InR, canary5InW, canary5StencilKernel⟩,
     ⟨canary5Step2InR, canary5Step2InW, canary5Step2Kernel⟩]
  have hValid : CausalSweepValid steps canary5InR := by
    refine ⟨hS1, fun _ h => h, hS2, ?_, True.intro⟩
    intro a ha
    dsimp only
    have hInR : canary5InR a = true := (canary5_inR_of_inW ha).1
    rw [hInR]
    rfl
  have hSw := causalSweep_sound steps canary5InR m hValid hInit
  exact ⟨hSw.1, hSw.2 0 rfl, hSw.2 15 rfl⟩

end Anneal.SpatialPinV2

end
