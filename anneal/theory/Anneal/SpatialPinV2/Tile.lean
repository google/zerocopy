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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Trusted.MirAst
public import Trusted.MirModel

public section

/-!
# SpatialPin v2: `CodecMeta` Registries, 2D Tiles, & `MBAFF` (`Tile`)

Zero-TCB symbolic 2D strided tile algebra, closure-free codec metadata
registries (`List CodecMeta`), 3-mode spatial pinning, multi-plane chroma
ceiling-shift bounds, and interlaced `MBAFF` field-row bounds over
`Trusted.MirAst.AllocId` and `Trusted.MirSemantics.Allocation`:

1. **Three-Mode Spatial Pinning & Closure-Free `List CodecMeta` Registries:**
   - `SpatialPinMode` (`.uninit`, `.readOnly`, `.readWrite`) with
     `modeCanRead`, `modeCanWrite`, `modeDuplicable`, and `SpatialPinModeStep`
     (duplicable `.readOnly` freezes without rational fractional permissions).
   - `CodecMeta` (pure closure-free metadata replacing function closures inside
     spatial state), `lookupCodecMeta`, `registryHasId`,
     `checkRegistryUniqueIds` (`List.foldr`, `0` `._unsafe_rec`), and
     `lookupCodecMeta_eq_of_mem_unique`.
2. **Signed-Stride 2D `SymbolicTile2D` & $O(1)$ `tileSplitRows` /
   `tileSplitCols` with `ownedSpan` Shedding:**
   - `StrideDir` (`.fwd` top-down vs. `.bwd` bottom-up negative stride) and
     `SymbolicTile2D` carrying `(allocId, base, width, height, elemSize,
     ownedSpan, absStride, dir)` with `width * elemSize ≤ ownedSpan ≤
     absStride`.
   - `tileAddr_injective`: proves coordinate injectivity for both `.fwd` and
     `.bwd` strides (`[propext]` only).
   - `tileSplitRows` and `tileSplitCols` enforce empty-split base guards (no
     out-of-bounds `base` advancement when `r = height`, `height = 0`, or
     `ownedSpan = 0` / `c * elemSize`) and shed row-tail padding from left to
     right on column splits (`tileSplitRows_wellFormed`,
     `tileSplitRows_disjoint`, `tileSplitRows_covers_iff`,
     `tileSplitCols_wellFormed`, `tileSplitCols_disjoint`,
     `tileSplitCols_covers_iff`).
   - `tileInOwned_lt_allocLen`: links `TileWellFormed`, `t.allocId =
     alloc.allocId`, and `tileMaxByteBound` directly to
     `Trusted.MirSemantics.Allocation.bytes.length` and backward non-underflow.
3. **Chroma Ceiling-Shift (`AV_CEIL_RSHIFT`) & Interlaced `MBAFF`
   `fieldActiveRows` Bounds:**
   - `chromaCeilShift_bounds_last_row` and
     `chromaFloorShift_underallocates_odd`.
   - `fieldActiveRows`, `fieldActiveRows_sum`, `mbaff_fieldRow_inBounds`, and
     `mbaff_bottom_ceil_oob_odd` (catching odd-height bottom-field OOB).

All authored definitions are computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`, `0` `decide`) and every authored declaration
compiles using at most `[propext]` (`0` `Classical.choice`, `0` `Quot.sound`).
-/

namespace Anneal.SpatialPinV2

open Trusted.MirAst Trusted.MirSemantics

/-! ## Part I: Three-Mode Spatial Pinning & `List CodecMeta` Registries -/

/-- Three-mode spatial pin permission lattice: uninitialized write-only entry
(`.uninit`), duplicable shared read-only freeze (`.readOnly`), and exclusive
initialized read-write access (`.readWrite`). -/
inductive SpatialPinMode where
  | uninit
  | readOnly
  | readWrite

/-- True iff `m` permits reading initialized bytes. -/
@[expose] def modeCanRead (m : SpatialPinMode) : Bool :=
  match m with
  | .uninit => false
  | .readOnly => true
  | .readWrite => true

/-- True iff `m` permits writing bytes. -/
@[expose] def modeCanWrite (m : SpatialPinMode) : Bool :=
  match m with
  | .uninit => true
  | .readOnly => false
  | .readWrite => true

/-- True iff `m` is duplicable across multiple read-only consumers without
fractional permissions. -/
@[expose] def modeDuplicable (m : SpatialPinMode) : Bool :=
  match m with
  | .uninit => false
  | .readOnly => true
  | .readWrite => false

/-- Valid one-step lifecycle transition on a spatial pin mode:
`.uninit → .readWrite` (initialization), `.readWrite → .readOnly` (freeze),
or reflexive preservation. -/
@[expose] def SpatialPinModeStep (m₁ m₂ : SpatialPinMode) : Prop :=
  m₁ = m₂ ∨ (m₁ = .uninit ∧ m₂ = .readWrite) ∨
    (m₁ = .readWrite ∧ m₂ = .readOnly)

/-- Once a pin is readable (`modeCanRead m₁ = true`), every valid
`SpatialPinModeStep` preserves readability (`[]` zero axioms). -/
theorem modeStep_preserves_canRead {m₁ m₂ : SpatialPinMode}
    (hStep : SpatialPinModeStep m₁ m₂) (hRead : modeCanRead m₁ = true) :
    modeCanRead m₂ = true := by
  cases hStep with
  | inl hEq => rw [← hEq]; exact hRead
  | inr hOr =>
    cases hOr with
    | inl hUW => rw [hUW.2]; rfl
    | inr hWR => rw [hWR.2]; rfl

/-- Only `.readOnly` is duplicable (`[]` zero axioms). -/
theorem modeDuplicable_iff_readOnly (m : SpatialPinMode) :
    modeDuplicable m = true ↔ m = .readOnly := by
  cases m with
  | uninit => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | readOnly => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | readWrite => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩

/-- Closure-free codec descriptor stored in a `List CodecMeta` registry instead
of embedding Lean function closures inside spatial maps. -/
structure CodecMeta where
  codecId : Nat
  byteLen : Nat
  alignLog2 : Nat
  elemSize : Nat

private theorem natBeq_refl_sp : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | n + 1 => natBeq_refl_sp n

private theorem natEq_of_beq_sp : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq_sp h)

/-- Computable lookup in a `List CodecMeta` registry by `codecId` via
`List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def lookupCodecMeta (reg : List CodecMeta) (id : Nat) :
    Option CodecMeta :=
  List.foldr
    (fun m acc => if Nat.beq m.codecId id then some m else acc)
    none reg

/-- Computable membership test for `codecId` in a `List CodecMeta` registry via
`List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def registryHasId (reg : List CodecMeta) (id : Nat) : Bool :=
  List.foldr (fun m ih => Nat.beq m.codecId id || ih) false reg

/-- Computable uniqueness check on a `List CodecMeta` registry via `List.foldr`
(`0` `._unsafe_rec`): returns `true` iff no two entries share a `codecId`. -/
@[expose] def checkRegistryUniqueIds (reg : List CodecMeta) : Bool :=
  (List.foldr
    (fun m acc =>
      (!registryHasId acc.2 m.codecId && acc.1, m :: acc.2))
    (true, [])
    reg).1

private theorem checkRegistryUniqueIds_snd :
    ∀ reg : List CodecMeta,
      (List.foldr
        (fun m acc =>
          (!registryHasId acc.2 m.codecId && acc.1, m :: acc.2))
        (true, [])
        reg).2 = reg
  | [] => rfl
  | m :: tl => congrArg (List.cons m) (checkRegistryUniqueIds_snd tl)

private theorem registryHasId_of_mem {m : CodecMeta} :
    ∀ {reg : List CodecMeta}, m ∈ reg → registryHasId reg m.codecId = true
  | _ :: _, .head _ => by
    change (Nat.beq m.codecId m.codecId || _) = true
    rw [natBeq_refl_sp m.codecId]
    rfl
  | hd :: tl, .tail _ hMem => by
    change (Nat.beq hd.codecId m.codecId || registryHasId tl m.codecId) = true
    rw [registryHasId_of_mem hMem]
    cases Nat.beq hd.codecId m.codecId <;> rfl

/-- Uniqueness soundness for `List CodecMeta` (`[]` zero axioms): when
`checkRegistryUniqueIds reg = true`, every member `m ∈ reg` is returned
unambiguously by `lookupCodecMeta reg m.codecId = some m` with zero shadowing.
-/
theorem lookupCodecMeta_eq_of_mem_unique :
    ∀ {reg : List CodecMeta} {m : CodecMeta},
      checkRegistryUniqueIds reg = true → m ∈ reg →
      lookupCodecMeta reg m.codecId = some m
  | [], _, _, hMem => nomatch hMem
  | hd :: tl, m, hUniq, hMem => by
    change
      (!registryHasId
          (List.foldr
            (fun x acc =>
              (!registryHasId acc.2 x.codecId && acc.1, x :: acc.2))
            (true, []) tl).2 hd.codecId &&
        checkRegistryUniqueIds tl) = true at hUniq
    rw [checkRegistryUniqueIds_snd tl] at hUniq
    cases hHas : registryHasId tl hd.codecId with
    | true =>
      rw [hHas] at hUniq
      exact Bool.noConfusion hUniq
    | false =>
      rw [hHas] at hUniq
      cases hMem with
      | head =>
        change (if Nat.beq hd.codecId hd.codecId then some hd else _) = some hd
        rw [natBeq_refl_sp hd.codecId]
        rfl
      | tail _ hTailMem =>
        change
          (if Nat.beq hd.codecId m.codecId then some hd
           else lookupCodecMeta tl m.codecId) = some m
        cases hEqId : Nat.beq hd.codecId m.codecId with
        | true =>
          have hSame : hd.codecId = m.codecId := natEq_of_beq_sp hEqId
          have hInTl : registryHasId tl hd.codecId = true := by
            rw [hSame]
            exact registryHasId_of_mem hTailMem
          rw [hHas] at hInTl
          exact Bool.noConfusion hInTl
        | false =>
          exact lookupCodecMeta_eq_of_mem_unique hUniq hTailMem

/-! ## Part II: Signed-Stride 2D `SymbolicTile2D` & $O(1)$ Splits -/

/-- Row-stride direction: `.fwd` advances by `+absStride` per row (top-down),
while `.bwd` steps by `-absStride` per row (bottom-up negative stride, e.g.,
FFmpeg `AVFrame::linesize < 0` or Halide inverted buffers). -/
inductive StrideDir where
  | fwd
  | bwd

/-- Symbolic 2D strided tile descriptor inside allocation `allocId`.
`ownedSpan` is the per-row owned byte width (`width * elemSize ≤ ownedSpan ≤
absStride`), separating active payload `[0, width * elemSize)` from trailing
row-padding `[width * elemSize, ownedSpan)`. -/
structure SymbolicTile2D where
  allocId : AllocId
  base : Nat
  width : Nat
  height : Nat
  elemSize : Nat
  ownedSpan : Nat
  absStride : Nat
  dir : StrideDir

/-- Byte offset of row `y` inside `t.allocId`. -/
@[expose] def tileRowAddr (t : SymbolicTile2D) (y : Nat) : Nat :=
  match t.dir with
  | .fwd => t.base + y * t.absStride
  | .bwd => t.base - y * t.absStride

/-- Byte offset of coordinate `(y, b)` inside `t.allocId`. -/
@[expose] def tileAddr (t : SymbolicTile2D) (y b : Nat) : Nat :=
  tileRowAddr t y + b

/-- Well-formedness of a `SymbolicTile2D`: active payload fits inside
`ownedSpan`, `ownedSpan` fits inside `absStride` (preventing inter-row overlap),
and backward-strided non-empty tiles stay non-negative (`(height - 1) *
absStride ≤ base`). -/
@[expose] def TileWellFormed (t : SymbolicTile2D) : Prop :=
  t.width * t.elemSize ≤ t.ownedSpan ∧
  t.ownedSpan ≤ t.absStride ∧
  (t.dir = .bwd → 0 < t.height → (t.height - 1) * t.absStride ≤ t.base)

/-- Owned-byte membership for `t`: `(aid, off)` lies in row `y < t.height` and
owned byte offset `b < t.ownedSpan`. -/
@[expose] def TileInOwned (t : SymbolicTile2D) (aid : AllocId)
    (off : Nat) : Prop :=
  t.allocId = aid ∧
    ∃ y b : Nat, y < t.height ∧ b < t.ownedSpan ∧ tileAddr t y b = off

private theorem natSub_add_cancel_sp :
    ∀ {k n : Nat}, k ≤ n → k + (n - k) = n
  | 0, n, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | k + 1, 0, h => nomatch h
  | k + 1, n + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_add]
    exact congrArg Nat.succ (natSub_add_cancel_sp (Nat.le_of_succ_le_succ h))

private theorem natLe_sub_of_add_le_sp {a b c : Nat} (h : a + b ≤ c) :
    a ≤ c - b := by
  have hSub := Nat.sub_le_sub_right h b
  rw [Nat.add_sub_cancel] at hSub
  exact hSub

private theorem natLe_of_lt_pred_sp {y h : Nat} (hy : y < h) : y ≤ h - 1 := by
  cases h with
  | zero => exact False.elim (Nat.not_lt_zero y hy)
  | succ h' =>
    rw [Nat.add_sub_cancel]
    exact Nat.le_of_lt_succ hy

private theorem bwd_row_step_le {base y₁ y₂ s : Nat}
    (hLt : y₁ < y₂) (hTop : y₂ * s ≤ base) :
    (base - y₂ * s) + s ≤ base - y₁ * s := by
  have hStep : y₁ * s + s ≤ y₂ * s := by
    have hMul := Nat.mul_le_mul_right s hLt
    rw [Nat.succ_mul] at hMul
    exact hMul
  have hY1Le : y₁ * s ≤ base := Nat.le_trans (Nat.le_add_right _ s)
    (Nat.le_trans hStep hTop)
  apply natLe_sub_of_add_le_sp
  have hAssoc :
      (base - y₂ * s) + s + y₁ * s = (base - y₂ * s) + (y₁ * s + s) := by
    rw [Nat.add_assoc, Nat.add_comm s (y₁ * s)]
  rw [hAssoc]
  exact Nat.le_trans (Nat.add_le_add_left hStep (base - y₂ * s))
    (by rw [Nat.add_comm (base - y₂ * s) (y₂ * s), natSub_add_cancel_sp hTop]
        exact Nat.le_refl base)

private theorem tileAddr_lt_of_row_lt {t : SymbolicTile2D}
    (hWf : TileWellFormed t) {y₁ y₂ b₁ b₂ : Nat}
    (hy₁ : y₁ < t.height) (hy₂ : y₂ < t.height)
    (hb₁ : b₁ < t.ownedSpan) (hb₂ : b₂ < t.ownedSpan)
    (hRowLt : y₁ < y₂) :
    tileAddr t y₁ b₁ ≠ tileAddr t y₂ b₂ := by
  cases hDir : t.dir with
  | fwd =>
    dsimp only [tileAddr, tileRowAddr]
    rw [hDir]
    have hStep : y₁ * t.absStride + t.absStride ≤ y₂ * t.absStride := by
      have hMul := Nat.mul_le_mul_right t.absStride hRowLt
      rw [Nat.succ_mul] at hMul
      exact hMul
    have h1 : t.base + y₁ * t.absStride + b₁ <
        t.base + y₁ * t.absStride + t.ownedSpan :=
      Nat.add_lt_add_left hb₁ (t.base + y₁ * t.absStride)
    have h2 : t.base + y₁ * t.absStride + t.ownedSpan ≤
        t.base + y₂ * t.absStride := by
      apply Nat.le_trans (Nat.add_le_add_left hWf.2.1 _)
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left hStep t.base
    have h3 : t.base + y₂ * t.absStride ≤ t.base + y₂ * t.absStride + b₂ :=
      Nat.le_add_right _ b₂
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3))
  | bwd =>
    dsimp only [tileAddr, tileRowAddr]
    rw [hDir]
    have hPosH : 0 < t.height := Nat.lt_of_le_of_lt (Nat.zero_le y₁) hy₁
    have hTop : y₂ * t.absStride ≤ t.base :=
      Nat.le_trans (Nat.mul_le_mul_right t.absStride (natLe_of_lt_pred_sp hy₂))
        (hWf.2.2 hDir hPosH)
    have hBwd := bwd_row_step_le hRowLt hTop
    have h1 : (t.base - y₂ * t.absStride) + b₂ <
        (t.base - y₂ * t.absStride) + t.ownedSpan :=
      Nat.add_lt_add_left hb₂ _
    have h2 : (t.base - y₂ * t.absStride) + t.ownedSpan ≤
        t.base - y₁ * t.absStride :=
      Nat.le_trans (Nat.add_le_add_left hWf.2.1 _) hBwd
    have h3 : t.base - y₁ * t.absStride ≤ (t.base - y₁ * t.absStride) + b₁ :=
      Nat.le_add_right _ b₁
    have hGt : (t.base - y₂ * t.absStride) + b₂ <
        (t.base - y₁ * t.absStride) + b₁ :=
      Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3)
    exact fun hEq => Nat.ne_of_lt hGt hEq.symm

/-- Coordinate injectivity of `SymbolicTile2D` for both `.fwd` and `.bwd`
strides (`[propext]` only): distinct `(y, b)` coordinates inside a well-formed
tile never alias the same byte offset. -/
theorem tileAddr_injective {t : SymbolicTile2D} (hWf : TileWellFormed t)
    {y₁ y₂ b₁ b₂ : Nat}
    (hy₁ : y₁ < t.height) (hy₂ : y₂ < t.height)
    (hb₁ : b₁ < t.ownedSpan) (hb₂ : b₂ < t.ownedSpan)
    (hEq : tileAddr t y₁ b₁ = tileAddr t y₂ b₂) :
    y₁ = y₂ ∧ b₁ = b₂ := by
  have hyEq : y₁ = y₂ := by
    cases Nat.lt_or_ge y₁ y₂ with
    | inl hLt =>
      exact False.elim (tileAddr_lt_of_row_lt hWf hy₁ hy₂ hb₁ hb₂ hLt hEq)
    | inr hGe =>
      cases Nat.lt_or_ge y₂ y₁ with
      | inl hGt =>
        exact False.elim
          (tileAddr_lt_of_row_lt hWf hy₂ hy₁ hb₂ hb₁ hGt hEq.symm)
      | inr hLe => exact Nat.le_antisymm hLe hGe
  rw [hyEq] at hEq
  exact ⟨hyEq, Nat.add_left_cancel hEq⟩

/-- $O(1)$ horizontal row split at row `r`, with the empty-split base guard
(`r = t.height || t.ownedSpan = 0`) preventing out-of-bounds `base` stepping
under backward (`.bwd`) strides or zero-span allocations. -/
@[expose] def tileSplitRows (t : SymbolicTile2D) (r : Nat) :
    SymbolicTile2D × SymbolicTile2D :=
  let botBase :=
    if Nat.beq r t.height || Nat.beq t.ownedSpan 0 then
      t.base
    else
      tileRowAddr t r
  ({ t with height := r }, { t with base := botBase, height := t.height - r })

private theorem tileRowAddr_shift_fwd (base s r y : Nat) :
    base + r * s + y * s = base + (r + y) * s := by
  rw [Nat.add_mul, Nat.add_assoc]

private theorem tileRowAddr_shift_bwd (base s r y : Nat) :
    base - r * s - y * s = base - (r + y) * s := by
  rw [Nat.sub_sub, Nat.add_mul]

/-- `tileSplitRows t r` preserves `TileWellFormed` on both halves whenever
`r ≤ t.height` (`[propext]` only). -/
theorem tileSplitRows_wellFormed {t : SymbolicTile2D} (hWf : TileWellFormed t)
    {r : Nat} (hr : r ≤ t.height) :
    TileWellFormed (tileSplitRows t r).1 ∧
    TileWellFormed (tileSplitRows t r).2 := by
  dsimp only [tileSplitRows, TileWellFormed]
  refine ⟨⟨hWf.1, hWf.2.1, ?_⟩, ⟨hWf.1, hWf.2.1, ?_⟩⟩
  · intro hBwd hPosR
    have hPosH : 0 < t.height := Nat.lt_of_lt_of_le hPosR hr
    exact Nat.le_trans
      (Nat.mul_le_mul_right t.absStride (Nat.sub_le_sub_right hr 1))
      (hWf.2.2 hBwd hPosH)
  · intro hBwd hPosBot
    have hRLt : r < t.height := by
      cases Nat.lt_or_ge r t.height with
      | inl h => exact h
      | inr hGe =>
        have hEq : r = t.height := Nat.le_antisymm hr hGe
        rw [hEq, Nat.sub_self] at hPosBot
        exact False.elim (Nat.lt_irrefl 0 hPosBot)
    have hNeR : Nat.beq r t.height = false := by
      cases hb : Nat.beq r t.height with
      | false => rfl
      | true =>
        exact False.elim (Nat.ne_of_lt hRLt (natEq_of_beq_sp hb))
    have hPosH : 0 < t.height := Nat.lt_of_le_of_lt (Nat.zero_le r) hRLt
    have hSubEq : r + (t.height - r - 1) = t.height - 1 := by
      have h1 : 1 ≤ t.height - r := hPosBot
      have h2 := natSub_add_cancel_sp h1
      have h3 := natSub_add_cancel_sp hr
      have hEq1 : (r + (t.height - r - 1)) + 1 = t.height := by
        rw [Nat.add_assoc, Nat.add_comm (t.height - r - 1) 1, h2, h3]
      have hSub := congrArg (fun x => x - 1) hEq1
      rw [Nat.add_sub_cancel] at hSub
      exact hSub
    cases hZSpan : Nat.beq t.ownedSpan 0 with
    | true =>
      rw [hNeR]
      change (t.height - r - 1) * t.absStride ≤ t.base
      exact Nat.le_trans
        (Nat.mul_le_mul_right t.absStride
          (Nat.sub_le_sub_right (Nat.sub_le t.height r) 1))
        (hWf.2.2 hBwd hPosH)
    | false =>
      rw [hNeR]
      change (t.height - r - 1) * t.absStride ≤ tileRowAddr t r
      dsimp only [tileRowAddr]
      rw [hBwd]
      apply natLe_sub_of_add_le_sp
      rw [Nat.add_comm, ← Nat.add_mul, hSubEq]
      exact hWf.2.2 hBwd hPosH

private theorem tileRowAddr_bot_eq {t : SymbolicTile2D} {r y b : Nat}
    (hy : y < t.height - r) (hb : b < t.ownedSpan) :
    tileAddr (tileSplitRows t r).2 y b = tileAddr t (r + y) b := by
  have hRLt : r < t.height := by
    cases Nat.lt_or_ge r t.height with
    | inl h => exact h
    | inr hGe =>
      have hZero : t.height - r = 0 := Nat.sub_eq_zero_of_le hGe
      rw [hZero] at hy
      exact False.elim (Nat.not_lt_zero y hy)
  have hNeR : Nat.beq r t.height = false := by
    cases h : Nat.beq r t.height with
    | false => rfl
    | true => exact False.elim (Nat.ne_of_lt hRLt (natEq_of_beq_sp h))
  have hNeSpan : Nat.beq t.ownedSpan 0 = false := by
    cases h : Nat.beq t.ownedSpan 0 with
    | false => rfl
    | true =>
      rw [natEq_of_beq_sp h] at hb
      exact False.elim (Nat.not_lt_zero b hb)
  dsimp only [tileAddr, tileSplitRows]
  rw [hNeR, hNeSpan]
  cases hDir : t.dir with
  | fwd =>
    dsimp only [tileRowAddr]
    rw [hDir]
    change t.base + r * t.absStride + y * t.absStride + b =
      t.base + (r + y) * t.absStride + b
    rw [tileRowAddr_shift_fwd]
  | bwd =>
    dsimp only [tileRowAddr]
    rw [hDir]
    change t.base - r * t.absStride - y * t.absStride + b =
      t.base - (r + y) * t.absStride + b
    rw [tileRowAddr_shift_bwd]

/-- Row-split disjointness (`[propext]` only): for any `TileWellFormed t` and
`r ≤ t.height`, the top and bottom tiles share no owned byte offset. -/
theorem tileSplitRows_disjoint {t : SymbolicTile2D} (hWf : TileWellFormed t)
    {r : Nat} (hr : r ≤ t.height) {aid : AllocId} {off : Nat}
    (hTop : TileInOwned (tileSplitRows t r).1 aid off)
    (hBot : TileInOwned (tileSplitRows t r).2 aid off) : False := by
  cases hTop.2 with
  | intro y₁ h1 =>
    cases h1 with
    | intro b₁ h1' =>
      cases hBot.2 with
      | intro y₂ h2 =>
        cases h2 with
        | intro b₂ h2' =>
          dsimp only [tileSplitRows] at h1' h2'
          have hAddrBot : tileAddr t (r + y₂) b₂ = off := by
            rw [← tileRowAddr_bot_eq h2'.1 h2'.2.1]
            exact h2'.2.2
          have hAddrTop : tileAddr t y₁ b₁ = off := h1'.2.2
          have hY1Lt : y₁ < t.height := Nat.lt_of_lt_of_le h1'.1 hr
          have hY2Lt : r + y₂ < t.height := by
            have hAdd := Nat.add_lt_add_left h2'.1 r
            rw [natSub_add_cancel_sp hr] at hAdd
            exact hAdd
          have hInj :=
            tileAddr_injective hWf hY1Lt hY2Lt h1'.2.1 h2'.2.1
              (Eq.trans hAddrTop hAddrBot.symm)
          have hGe : r ≤ y₁ := by
            rw [hInj.1]
            exact Nat.le_add_right r y₂
          exact Nat.not_lt_of_ge hGe h1'.1

/-- Row-split exact coverage (`[propext]` only): `TileInOwned t aid off` holds
iff `(aid, off)` lies in the top half or the bottom half. -/
theorem tileSplitRows_covers_iff {t : SymbolicTile2D} {r : Nat}
    (hr : r ≤ t.height) (aid : AllocId) (off : Nat) :
    TileInOwned t aid off ↔
      TileInOwned (tileSplitRows t r).1 aid off ∨
      TileInOwned (tileSplitRows t r).2 aid off := by
  refine ⟨?_, ?_⟩
  · intro hIn
    cases hIn.2 with
    | intro y hy =>
      cases hy with
      | intro b hb =>
        cases Nat.lt_or_ge y r with
        | inl hLt =>
          exact Or.inl ⟨hIn.1, y, b, hLt, hb.2.1, hb.2.2⟩
        | inr hGe =>
          right
          have hSubLt : y - r < t.height - r := Nat.sub_lt_sub_right hGe hb.1
          refine ⟨hIn.1, y - r, b, hSubLt, hb.2.1, ?_⟩
          rw [tileRowAddr_bot_eq hSubLt hb.2.1, natSub_add_cancel_sp hGe]
          exact hb.2.2
  · intro hOr
    cases hOr with
    | inl hTop =>
      cases hTop.2 with
      | intro y hy =>
        cases hy with
        | intro b hb =>
          dsimp only [tileSplitRows] at hb
          exact ⟨hTop.1, y, b, Nat.lt_of_lt_of_le hb.1 hr, hb.2.1, hb.2.2⟩
    | inr hBot =>
      cases hBot.2 with
      | intro y hy =>
        cases hy with
        | intro b hb =>
          dsimp only [tileSplitRows] at hb
          have hYlt : r + y < t.height := by
            have hAdd := Nat.add_lt_add_left hb.1 r
            rw [natSub_add_cancel_sp hr] at hAdd
            exact hAdd
          refine ⟨hBot.1, r + y, b, hYlt, hb.2.1, ?_⟩
          rw [← tileRowAddr_bot_eq hb.1 hb.2.1]
          exact hb.2.2

/-- $O(1)$ vertical column split at column `c` with `ownedSpan` shedding: the
left tile shrinks `ownedSpan` to `c * elemSize` while the right tile receives
`t.ownedSpan - c * elemSize` (including all trailing row-padding bytes), with
the empty-split base guard (`t.height = 0 || t.ownedSpan = c * elemSize`). -/
@[expose] def tileSplitCols (t : SymbolicTile2D) (c : Nat) :
    SymbolicTile2D × SymbolicTile2D :=
  let lb := c * t.elemSize
  let rightBase :=
    if Nat.beq t.height 0 || Nat.beq t.ownedSpan lb then
      t.base
    else
      t.base + lb
  ({ t with width := c, ownedSpan := lb },
   { t with base := rightBase, width := t.width - c,
            ownedSpan := t.ownedSpan - lb })

/-- `tileSplitCols t c` preserves `TileWellFormed` on both halves whenever
`c ≤ t.width` (`[propext]` only). -/
theorem tileSplitCols_wellFormed {t : SymbolicTile2D} (hWf : TileWellFormed t)
    {c : Nat} (hc : c ≤ t.width) :
    TileWellFormed (tileSplitCols t c).1 ∧
    TileWellFormed (tileSplitCols t c).2 := by
  have hLbLeAct : c * t.elemSize ≤ t.width * t.elemSize :=
    Nat.mul_le_mul_right t.elemSize hc
  have hLbLeSpan : c * t.elemSize ≤ t.ownedSpan :=
    Nat.le_trans hLbLeAct hWf.1
  dsimp only [tileSplitCols, TileWellFormed]
  refine ⟨⟨Nat.le_refl _, Nat.le_trans hLbLeSpan hWf.2.1, hWf.2.2⟩,
    ⟨?_, Nat.le_trans (Nat.sub_le t.ownedSpan _) hWf.2.1, ?_⟩⟩
  · apply natLe_sub_of_add_le_sp
    rw [← Nat.add_mul, Nat.add_comm (t.width - c) c, natSub_add_cancel_sp hc]
    exact hWf.1
  · intro hBwd hPosH
    have hBaseLe :
        t.base ≤
          (if Nat.beq t.height 0 || Nat.beq t.ownedSpan (c * t.elemSize) then
            t.base
          else
            t.base + c * t.elemSize) := by
      cases Nat.beq t.height 0 <;>
        cases Nat.beq t.ownedSpan (c * t.elemSize) <;>
        first | exact Nat.le_refl t.base | exact Nat.le_add_right t.base _
    exact Nat.le_trans (hWf.2.2 hBwd hPosH) hBaseLe

private theorem tileAddr_rightCol_eq {t : SymbolicTile2D}
    (hWf : TileWellFormed t) {c y b : Nat}
    (hy : y < t.height) (hb : b < t.ownedSpan - c * t.elemSize) :
    tileAddr (tileSplitCols t c).2 y b = tileAddr t y (c * t.elemSize + b) := by
  have hNeH : Nat.beq t.height 0 = false := by
    cases h : Nat.beq t.height 0 with
    | false => rfl
    | true =>
      rw [natEq_of_beq_sp h] at hy
      exact False.elim (Nat.not_lt_zero y hy)
  have hNeSpan : Nat.beq t.ownedSpan (c * t.elemSize) = false := by
    cases h : Nat.beq t.ownedSpan (c * t.elemSize) with
    | false => rfl
    | true =>
      rw [natEq_of_beq_sp h, Nat.sub_self] at hb
      exact False.elim (Nat.not_lt_zero b hb)
  dsimp only [tileAddr, tileSplitCols]
  rw [hNeH, hNeSpan]
  cases hDir : t.dir with
  | fwd =>
    dsimp only [tileRowAddr]
    rw [hDir]
    change t.base + c * t.elemSize + y * t.absStride + b =
      t.base + y * t.absStride + (c * t.elemSize + b)
    rw [Nat.add_right_comm t.base (c * t.elemSize) (y * t.absStride),
      Nat.add_assoc]
  | bwd =>
    dsimp only [tileRowAddr]
    rw [hDir]
    change (t.base + c * t.elemSize - y * t.absStride) + b =
      (t.base - y * t.absStride) + (c * t.elemSize + b)
    have hPosH : 0 < t.height := Nat.lt_of_le_of_lt (Nat.zero_le y) hy
    have hTop : y * t.absStride ≤ t.base :=
      Nat.le_trans (Nat.mul_le_mul_right t.absStride (natLe_of_lt_pred_sp hy))
        (hWf.2.2 hDir hPosH)
    have hSubAdd :
        t.base + c * t.elemSize - y * t.absStride =
          (t.base - y * t.absStride) + c * t.elemSize := by
      rw [Nat.add_comm t.base (c * t.elemSize), Nat.add_sub_assoc hTop,
        Nat.add_comm (c * t.elemSize)]
    rw [hSubAdd, Nat.add_assoc]

/-- Column-split disjointness with `ownedSpan` shedding (`[propext]` only):
for any `TileWellFormed t` and `c ≤ t.width`, the left and right tiles share no
owned byte offset. -/
theorem tileSplitCols_disjoint {t : SymbolicTile2D} (hWf : TileWellFormed t)
    {c : Nat} (hc : c ≤ t.width) {aid : AllocId} {off : Nat}
    (hLeft : TileInOwned (tileSplitCols t c).1 aid off)
    (hRight : TileInOwned (tileSplitCols t c).2 aid off) : False := by
  have hLbLeSpan : c * t.elemSize ≤ t.ownedSpan :=
    Nat.le_trans (Nat.mul_le_mul_right t.elemSize hc) hWf.1
  cases hLeft.2 with
  | intro y₁ h1 =>
    cases h1 with
    | intro b₁ h1' =>
      cases hRight.2 with
      | intro y₂ h2 =>
        cases h2 with
        | intro b₂ h2' =>
          dsimp only [tileSplitCols] at h1' h2'
          have hAddrR : tileAddr t y₂ (c * t.elemSize + b₂) = off := by
            rw [← tileAddr_rightCol_eq hWf h2'.1 h2'.2.1]
            exact h2'.2.2
          have hB1Lt : b₁ < t.ownedSpan := Nat.lt_of_lt_of_le h1'.2.1 hLbLeSpan
          have hB2Lt : c * t.elemSize + b₂ < t.ownedSpan := by
            have hAdd := Nat.add_lt_add_left h2'.2.1 (c * t.elemSize)
            rw [natSub_add_cancel_sp hLbLeSpan] at hAdd
            exact hAdd
          have hInj :=
            tileAddr_injective hWf h1'.1 h2'.1 hB1Lt hB2Lt
              (Eq.trans h1'.2.2 hAddrR.symm)
          have hGe : c * t.elemSize ≤ b₁ := by
            rw [hInj.2]
            exact Nat.le_add_right (c * t.elemSize) b₂
          exact Nat.not_lt_of_ge hGe h1'.2.1

/-- Column-split exact coverage (`[propext]` only): under `TileWellFormed t`
and `c ≤ t.width`, `TileInOwned t aid off` holds iff `(aid, off)` lies in the
left tile or the right tile. -/
theorem tileSplitCols_covers_iff {t : SymbolicTile2D} (hWf : TileWellFormed t)
    {c : Nat} (hc : c ≤ t.width) (aid : AllocId) (off : Nat) :
    TileInOwned t aid off ↔
      TileInOwned (tileSplitCols t c).1 aid off ∨
      TileInOwned (tileSplitCols t c).2 aid off := by
  have hLbLeSpan : c * t.elemSize ≤ t.ownedSpan :=
    Nat.le_trans (Nat.mul_le_mul_right t.elemSize hc) hWf.1
  refine ⟨?_, ?_⟩
  · intro hIn
    cases hIn.2 with
    | intro y hy =>
      cases hy with
      | intro b hb =>
        cases Nat.lt_or_ge b (c * t.elemSize) with
        | inl hLt =>
          exact Or.inl ⟨hIn.1, y, b, hb.1, hLt, hb.2.2⟩
        | inr hGe =>
          right
          have hSubLt : b - c * t.elemSize < t.ownedSpan - c * t.elemSize :=
            Nat.sub_lt_sub_right hGe hb.2.1
          refine ⟨hIn.1, y, b - c * t.elemSize, hb.1, hSubLt, ?_⟩
          rw [tileAddr_rightCol_eq hWf hb.1 hSubLt,
            natSub_add_cancel_sp hGe]
          exact hb.2.2
  · intro hOr
    cases hOr with
    | inl hL =>
      cases hL.2 with
      | intro y hy =>
        cases hy with
        | intro b hb =>
          dsimp only [tileSplitCols] at hb
          exact ⟨hL.1, y, b, hb.1, Nat.lt_of_lt_of_le hb.2.1 hLbLeSpan, hb.2.2⟩
    | inr hR =>
      cases hR.2 with
      | intro y hy =>
        cases hy with
        | intro b hb =>
          dsimp only [tileSplitCols] at hb
          have hBlt : c * t.elemSize + b < t.ownedSpan := by
            have hAdd := Nat.add_lt_add_left hb.2.1 (c * t.elemSize)
            rw [natSub_add_cancel_sp hLbLeSpan] at hAdd
            exact hAdd
          refine ⟨hR.1, y, c * t.elemSize + b, hb.1, hBlt, ?_⟩
          rw [← tileAddr_rightCol_eq hWf hb.1 hb.2.1]
          exact hb.2.2

/-- Exact exclusive upper byte bound of a non-empty `SymbolicTile2D` inside its
backing `Allocation` (`0` when `t.height = 0` or `t.ownedSpan = 0`). -/
@[expose] def tileMaxByteBound (t : SymbolicTile2D) : Nat :=
  if Nat.beq t.height 0 || Nat.beq t.ownedSpan 0 then
    0
  else
    match t.dir with
    | .fwd => t.base + (t.height - 1) * t.absStride + t.ownedSpan
    | .bwd => t.base + t.ownedSpan

/-- `Trusted.MirSemantics.Allocation` bounds bridge (`[propext]` only): for any
well-formed tile `t` targeting `alloc` (`t.allocId = alloc.allocId`) with
`tileMaxByteBound t ≤ alloc.bytes.length`, every owned coordinate `(aid, off)`
targets `alloc.allocId`, lies strictly below `alloc.bytes.length`, and (under
`.bwd` strides) never underflows `t.base`. -/
theorem tileInOwned_lt_allocLen {t : SymbolicTile2D} {alloc : Allocation}
    (hWf : TileWellFormed t) (hAid : t.allocId = alloc.allocId)
    (hBound : tileMaxByteBound t ≤ alloc.bytes.length)
    {aid : AllocId} {off : Nat} (hIn : TileInOwned t aid off) :
    aid = alloc.allocId ∧
    off < alloc.bytes.length ∧
    (t.dir = .bwd → (t.height - 1) * t.absStride ≤ t.base) := by
  cases hIn.2 with
  | intro y hy =>
    cases hy with
    | intro b hb =>
      have hPosH : 0 < t.height := Nat.lt_of_le_of_lt (Nat.zero_le y) hb.1
      have hAidEq : aid = alloc.allocId := Eq.trans hIn.1.symm hAid
      have hBwdSafe : t.dir = .bwd → (t.height - 1) * t.absStride ≤ t.base :=
        fun hDir => hWf.2.2 hDir hPosH
      have hNeH : Nat.beq t.height 0 = false := by
        cases h : Nat.beq t.height 0 with
        | false => rfl
        | true =>
          rw [natEq_of_beq_sp h] at hb
          exact False.elim (Nat.not_lt_zero y hb.1)
      have hNeS : Nat.beq t.ownedSpan 0 = false := by
        cases h : Nat.beq t.ownedSpan 0 with
        | false => rfl
        | true =>
          rw [natEq_of_beq_sp h] at hb
          exact False.elim (Nat.not_lt_zero b hb.2.1)
      dsimp only [tileMaxByteBound] at hBound
      rw [hNeH, hNeS] at hBound
      rw [← hb.2.2]
      refine ⟨hAidEq, ?_, hBwdSafe⟩
      cases hDir : t.dir with
      | fwd =>
        rw [hDir] at hBound
        dsimp only [tileAddr, tileRowAddr]
        rw [hDir]
        have hYLe : y * t.absStride ≤ (t.height - 1) * t.absStride :=
          Nat.mul_le_mul_right t.absStride (natLe_of_lt_pred_sp hb.1)
        have h1 : t.base + y * t.absStride + b <
            t.base + (t.height - 1) * t.absStride + t.ownedSpan :=
          Nat.lt_of_lt_of_le
            (Nat.add_lt_add_left hb.2.1 _)
            (Nat.add_le_add_right (Nat.add_le_add_left hYLe t.base) t.ownedSpan)
        exact Nat.lt_of_lt_of_le h1 hBound
      | bwd =>
        rw [hDir] at hBound
        dsimp only [tileAddr, tileRowAddr]
        rw [hDir]
        have hSubLe : t.base - y * t.absStride ≤ t.base :=
          Nat.sub_le t.base _
        have h1 : (t.base - y * t.absStride) + b < t.base + t.ownedSpan :=
          Nat.lt_of_lt_of_le
            (Nat.add_lt_add_left hb.2.1 _)
            (Nat.add_le_add_right hSubLe t.ownedSpan)
        exact Nat.lt_of_lt_of_le h1 hBound

/-! ## Part III: Chroma Ceiling-Shift (`AV_CEIL_RSHIFT`) & `MBAFF` Fields -/

/-- Normative chroma ceiling-shift dimension `⌈dim / 2^ss⌉` for `ss ∈ {0, 1}`
(matching 4:4:4 / 4:2:0 `AV_CEIL_RSHIFT`): returns `dim` for `ss = 0` and
`Nat.div (dim + 1) 2` for `ss ≥ 1` (`chromaCeilShift_bounds_last_row` enforces
`ss ≤ 1`). -/
@[expose] def chromaCeilShift (dim ss : Nat) : Nat :=
  match ss with
  | 0 => dim
  | _ => Nat.div (dim + 1) 2

private theorem natDiv2_succ_succ (n : Nat) :
    Nat.div (n + 2) 2 = Nat.div n 2 + 1 := by
  have hPos : 0 < 2 := Nat.succ_pos 1
  exact Nat.add_div_right n hPos

private theorem natDiv2_double (k : Nat) : Nat.div (2 * k) 2 = k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    have hEq : 2 * (k' + 1) = 2 * k' + 2 := Nat.mul_succ 2 k'
    rw [hEq, natDiv2_succ_succ, ih]

private theorem natDiv2_double_succ (k : Nat) : Nat.div (2 * k + 1) 2 = k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    have hEq : 2 * (k' + 1) + 1 = (2 * k' + 1) + 2 := by
      rw [Nat.mul_succ, Nat.add_right_comm]
    rw [hEq, natDiv2_succ_succ, ih]

private theorem nat_even_or_odd (n : Nat) :
    (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m ih =>
    cases ih with
    | inl hEv =>
      cases hEv with
      | intro k hk => exact Or.inr ⟨k, by rw [hk]⟩
    | inr hOd =>
      cases hOd with
      | intro k hk =>
        exact Or.inl ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- Normative chroma ceiling-shift bounds the last accessed chroma row for any
`0 < h` and `ss ≤ 1` (`[propext]` only). -/
theorem chromaCeilShift_bounds_last_row {h ss : Nat} (hh : 0 < h)
    (hss : ss ≤ 1) :
    Nat.div (h - 1) (Nat.pow 2 ss) < chromaCeilShift h ss := by
  cases ss with
  | zero =>
    change Nat.div (h - 1) 1 < h
    have hDiv1 : Nat.div (h - 1) 1 = h - 1 := Nat.div_one (h - 1)
    rw [hDiv1]
    exact Nat.sub_lt hh (Nat.zero_lt_one)
  | succ s =>
    cases s with
    | succ _ =>
      exact False.elim (Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ hss))
    | zero =>
      dsimp only [chromaCeilShift]
      change Nat.div (h - 1) 2 < Nat.div (h + 1) 2
      have hSub2 : h + 1 = (h - 1) + 2 := by
        have h1 : 1 ≤ h := hh
        have hC := natSub_add_cancel_sp h1
        rw [Nat.add_comm 1 (h - 1)] at hC
        have h2 : (h - 1) + 2 = ((h - 1) + 1) + 1 := rfl
        rw [h2, hC]
      rw [hSub2, natDiv2_succ_succ]
      exact Nat.lt_succ_self _

/-- Floor-shifting `h / 2` under-allocates chroma by 1 row on every odd luma
height `2 * k + 1` (`[propext]` only). -/
theorem chromaFloorShift_underallocates_odd (k : Nat) :
    Nat.div ((2 * k + 1) - 1) 2 = Nat.div (2 * k + 1) 2 ∧
    ¬ (Nat.div ((2 * k + 1) - 1) 2 < Nat.div (2 * k + 1) 2) := by
  have hEq : Nat.div ((2 * k + 1) - 1) 2 = Nat.div (2 * k + 1) 2 := by
    rw [Nat.add_sub_cancel, natDiv2_double, natDiv2_double_succ]
  exact ⟨hEq, fun hLt => by rw [hEq] at hLt; exact Nat.lt_irrefl _ hLt⟩

/-- Interlaced `MBAFF` active field row count: top field (`isBottom = false`)
receives `⌈planeH / 2⌉` even rows (`0, 2, ...`), while bottom field
(`isBottom = true`) receives `⌊planeH / 2⌋` odd rows (`1, 3, ...`). -/
@[expose] def fieldActiveRows (planeH : Nat) (isBottom : Bool) : Nat :=
  if isBottom then Nat.div planeH 2 else Nat.div (planeH + 1) 2

/-- Top and bottom `MBAFF` active field row counts partition `planeH` exactly
(`[propext]` only). -/
theorem fieldActiveRows_sum (planeH : Nat) :
    fieldActiveRows planeH false + fieldActiveRows planeH true = planeH := by
  change Nat.div (planeH + 1) 2 + Nat.div planeH 2 = planeH
  cases nat_even_or_odd planeH with
  | inl hEv =>
    cases hEv with
    | intro k hk =>
      rw [hk, natDiv2_double_succ, natDiv2_double, Nat.two_mul]
  | inr hOd =>
    cases hOd with
    | intro k hk =>
      have hPlus : 2 * k + 1 + 1 = 2 * (k + 1) := by rw [Nat.mul_succ]
      rw [hk, hPlus, natDiv2_double, natDiv2_double_succ, Nat.succ_add,
        Nat.two_mul]

/-- `MBAFF` frame-row bounds soundness (`[propext]` only): top-field row `y`
maps to even frame row `2 * y < planeH`, and bottom-field row `y` maps to odd
frame row `2 * y + 1 < planeH`. -/
theorem mbaff_fieldRow_inBounds (planeH y : Nat) :
    (y < fieldActiveRows planeH false → 2 * y < planeH) ∧
    (y < fieldActiveRows planeH true → 2 * y + 1 < planeH) := by
  refine ⟨?_, ?_⟩
  · intro hy
    change y < Nat.div (planeH + 1) 2 at hy
    cases nat_even_or_odd planeH with
    | inl hEv =>
      cases hEv with
      | intro k hk =>
        rw [hk, natDiv2_double_succ] at hy
        rw [hk]
        exact Nat.mul_lt_mul_of_pos_left hy (Nat.succ_pos 1)
    | inr hOd =>
      cases hOd with
      | intro k hk =>
        have hPlus : 2 * k + 1 + 1 = 2 * (k + 1) := by rw [Nat.mul_succ]
        rw [hk, hPlus, natDiv2_double] at hy
        rw [hk]
        have hLe : y ≤ k := Nat.le_of_lt_succ hy
        exact Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 hLe)
  · intro hy
    change y < Nat.div planeH 2 at hy
    cases nat_even_or_odd planeH with
    | inl hEv =>
      cases hEv with
      | intro k hk =>
        rw [hk, natDiv2_double] at hy
        rw [hk]
        have hLe : y + 1 ≤ k := hy
        have hMul := Nat.mul_le_mul_left 2 hLe
        rw [Nat.mul_succ] at hMul
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (2 * y + 1)) hMul
    | inr hOd =>
      cases hOd with
      | intro k hk =>
        rw [hk, natDiv2_double_succ] at hy
        rw [hk]
        exact Nat.add_lt_add_right
          (Nat.mul_lt_mul_of_pos_left hy (Nat.succ_pos 1)) 1

/-- Odd-height `MBAFF` bottom-field OOB catch (`[propext]` only): on any odd
plane height `2 * k + 1` (e.g., `4:2:0` chroma height `3` for luma height `6`),
using the top-field ceiling count `fieldActiveRows (2 * k + 1) false = k + 1`
for the bottom field admits `y = k < fieldActiveRows (2 * k + 1) false`, whose
odd frame row `2 * y + 1` is out of bounds (`¬ (2 * y + 1 < 2 * k + 1)`). -/
theorem mbaff_bottom_ceil_oob_odd (k : Nat) :
    fieldActiveRows (2 * k + 1) true = k ∧
    fieldActiveRows (2 * k + 1) false = k + 1 ∧
    (∃ y : Nat,
      y < fieldActiveRows (2 * k + 1) false ∧ ¬ (2 * y + 1 < 2 * k + 1)) := by
  have hTrue : fieldActiveRows (2 * k + 1) true = k := by
    change Nat.div (2 * k + 1) 2 = k
    exact natDiv2_double_succ k
  have hFalse : fieldActiveRows (2 * k + 1) false = k + 1 := by
    change Nat.div (2 * k + 1 + 1) 2 = k + 1
    have hPlus : 2 * k + 1 + 1 = 2 * (k + 1) := by rw [Nat.mul_succ]
    rw [hPlus, natDiv2_double]
  refine ⟨hTrue, hFalse, k, ?_, Nat.lt_irrefl _⟩
  rw [hFalse]
  exact Nat.lt_succ_self k

end Anneal.SpatialPinV2

end
