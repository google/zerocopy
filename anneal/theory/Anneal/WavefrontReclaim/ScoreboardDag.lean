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
public import Init.SimpLemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic

public section

/-!
# Multi-Predecessor Scoreboard DAGs, Halo Bounds, and Monotone Slots
(`Anneal.WavefrontReclaim.ScoreboardDag`)

Zero-TCB Pass-1-portable (`prelude` + `Init.*` only, `0` `noncomputable`,
`0` `._unsafe_rec`, `0` `omega`, `0` `by_cases`, `0` `decide`,
`0` `Classical.choice`) wavefront abstractions addressing multi-threaded
frame/slice codec requirements beyond `WavefrontReclaim`'s spawn-tree model:

1. **Edge-clamped 2D halo progress bounds (`neededRowEdge`)**: guarantees both
   Row-0 race immunity (`1 ≤ neededRowEdge`) and bottom-edge deadlock freedom
   (`neededRowEdge ≤ hRef`) whenever `1 ≤ hRef`, even for negative or
   out-of-frame motion vectors.
2. **Packed `MonotoneSlotWord` & non-cancellative prefix witness lattice**:
   encodes `(poisoned : 1, hasWaiters : 1, publishedRow : 30)` with the
   `< 2^30` row bound carried intrinsically on `SlotState` (plus fail-closed
   `mkSlotState?` / `packSlotWord?` constructors rejecting `≥ 2^30` rows),
   proves unconditional pack/unpack round-tripping and `< 2^32` word bounds,
   and proves `RowPrefixReady` persistence under `(poisoned, publishedRow)`
   monotonic steps even while `hasWaiters` toggles non-monotonically.
3. **Constructive minimal-rank DAG scoreboard liveness (`findMinRankBelow`,
   `scoreboard_progress_witness`)**: extracts an enabled unfinished task with
   zero `Classical.choice` for any `ValidDagRank`, plus concrete rank functions
   for HEVC/AV1 WPP (`wppRank`) and multi-stage VVC backward-halo CTU
   scoreboards (`vvcCtuRank`, handling `(rx+1, ry+1)` cross-stage Moore
   neighborhoods).
-/

namespace Anneal.WavefrontReclaim

/-! ## Part I: Edge-Clamped 2D Halo Progress Bounds -/

/-- Total minimum on `Nat` (`Nat.ble`-based, locked-`Init` portable). -/
@[expose] def natMin (a b : Nat) : Nat :=
  if Nat.ble a b then a else b

/-- Total maximum on `Nat` (`Nat.ble`-based, locked-`Init` portable). -/
@[expose] def natMax (a b : Nat) : Nat :=
  if Nat.ble a b then b else a

theorem natMin_le_left (a b : Nat) : natMin a b ≤ a := by
  dsimp only [natMin]
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl a
  | false =>
    cases Nat.lt_or_ge b a with
    | inl hLt => exact Nat.le_of_lt hLt
    | inr hGe =>
      have hT : Nat.ble a b = true := Nat.ble_eq_true_of_le hGe
      rw [hT] at h
      exact Bool.noConfusion h

theorem le_natMin {c a b : Nat} (ha : c ≤ a) (hb : c ≤ b) :
    c ≤ natMin a b := by
  dsimp only [natMin]
  cases Nat.ble a b with
  | true => exact ha
  | false => exact hb

theorem natMin_eq_right {a b : Nat} (h : b ≤ a) : natMin a b = b := by
  dsimp only [natMin]
  cases hBle : Nat.ble a b with
  | false => rfl
  | true => exact Nat.le_antisymm (Nat.le_of_ble_eq_true hBle) h

theorem le_natMax_left (a b : Nat) : a ≤ natMax a b := by
  dsimp only [natMax]
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact Nat.le_refl a

theorem natMax_eq_right {a b : Nat} (h : a ≤ b) : natMax a b = b := by
  dsimp only [natMax]
  have hT : Nat.ble a b = true := Nat.ble_eq_true_of_le h
  rw [hT]
  rfl

/-- Clamp an `Int` coordinate below at `0`, mapping negative values to `0`. -/
@[expose] def clampIntNonneg (x : Int) : Nat :=
  match x with
  | .ofNat n => n
  | .negSucc _ => 0

theorem clampIntNonneg_ofNat (n : Nat) : clampIntNonneg (.ofNat n) = n := rfl

theorem clampIntNonneg_negSucc (m : Nat) : clampIntNonneg (.negSucc m) = 0 := rfl

/-- Minimum required published reference row for a motion-compensated block:
`natMin hRef` applied to
`natMax 1 (clampIntNonneg (yMax + Int.ofNat (haloDown + 1))) + lag`. -/
@[expose] def neededRowEdge (yMax : Int) (haloDown lag hRef : Nat) : Nat :=
  natMin hRef
    (natMax 1 (clampIntNonneg (yMax + Int.ofNat (haloDown + 1))) + lag)

/-- Bottom-edge ceiling deadlock freedom: `neededRowEdge` never exceeds `hRef`.
-/
theorem neededRowEdge_le_hRef (yMax : Int) (haloDown lag hRef : Nat) :
    neededRowEdge yMax haloDown lag hRef ≤ hRef :=
  natMin_le_left hRef _

/-- Top-edge Row-0 race prevention: whenever `1 ≤ hRef`, at least row `1` is
required even when `yMax` is arbitrarily negative. -/
theorem one_le_neededRowEdge {hRef : Nat} (hh : 1 ≤ hRef)
    (yMax : Int) (haloDown lag : Nat) :
    1 ≤ neededRowEdge yMax haloDown lag hRef :=
  le_natMin hh
    (Nat.le_trans (le_natMax_left 1 _) (Nat.le_add_right _ lag))

/-- Combined upper and lower edge-clamped progress bounds. -/
theorem neededRowEdge_bounds {hRef : Nat} (hh : 1 ≤ hRef)
    (yMax : Int) (haloDown lag : Nat) :
    1 ≤ neededRowEdge yMax haloDown lag hRef ∧
      neededRowEdge yMax haloDown lag hRef ≤ hRef :=
  ⟨one_le_neededRowEdge hh yMax haloDown lag,
   neededRowEdge_le_hRef yMax haloDown lag hRef⟩

/-- Inside frame bounds, non-negative `yMax = Int.ofNat n` enforces the full
`n + haloDown + 1 + lag` margin without under-waiting. -/
theorem neededRowEdge_preserves_inbounds_margin
    (n haloDown lag hRef : Nat)
    (hIn : n + haloDown + 1 + lag ≤ hRef) :
    neededRowEdge (Int.ofNat n) haloDown lag hRef = n + haloDown + 1 + lag := by
  have hClamp :
      clampIntNonneg (Int.ofNat n + Int.ofNat (haloDown + 1)) =
        n + haloDown + 1 := by
    have hSum :
        Int.ofNat n + Int.ofNat (haloDown + 1) =
          Int.ofNat (n + (haloDown + 1)) := rfl
    rw [hSum]
    dsimp only [clampIntNonneg]
    exact (Nat.add_assoc n haloDown 1).symm
  have hMax1 : 1 ≤ n + haloDown + 1 :=
    Nat.le_add_left 1 (n + haloDown)
  have hMaxEq : natMax 1 (n + haloDown + 1) = n + haloDown + 1 :=
    natMax_eq_right hMax1
  have hNeeded :
      neededRowEdge (Int.ofNat n) haloDown lag hRef =
        natMin hRef (n + haloDown + 1 + lag) := by
    dsimp only [neededRowEdge]
    rw [hClamp, hMaxEq]
  rw [hNeeded]
  exact natMin_eq_right hIn

/-! ## Part II: Packed `MonotoneSlotWord` and Persistent Prefix Witness -/

@[expose] def slotRowCap : Nat := 1073741824       -- 2^30
@[expose] def slotWaitersBit : Nat := 1073741824   -- 1 <<< 30
@[expose] def slotPoisonBit : Nat := 2147483648    -- 1 <<< 31
@[expose] def slotWordCap : Nat := 4294967296      -- 2^32

theorem slotRowCap_pos : 0 < slotRowCap :=
  Nat.le_of_ble_eq_true (rfl : Nat.ble 1 slotRowCap = true)

private theorem slotPoisonBit_pos : 0 < slotPoisonBit :=
  Nat.le_of_ble_eq_true (rfl : Nat.ble 1 slotPoisonBit = true)

private theorem slotRowCap_le_slotPoisonBit : slotRowCap ≤ slotPoisonBit :=
  Nat.le_of_ble_eq_true (rfl : Nat.ble slotRowCap slotPoisonBit = true)

private theorem slotWaiters_add_cap_le_poison :
    slotWaitersBit + slotRowCap ≤ slotPoisonBit :=
  Nat.le_of_ble_eq_true
    (rfl : Nat.ble (slotWaitersBit + slotRowCap) slotPoisonBit = true)

private theorem slotAllFlags_add_cap_le_wordCap :
    slotPoisonBit + slotWaitersBit + slotRowCap ≤ slotWordCap :=
  Nat.le_of_ble_eq_true
    (rfl : Nat.ble (slotPoisonBit + slotWaitersBit + slotRowCap)
      slotWordCap = true)

/-- Validated logical state of a packed 32-bit `MonotonePublicationSlot`.
Carries `rowLtCap : publishedRow < slotRowCap` intrinsically so out-of-range
row counts that would collide with `hasWaiters`/`poisoned` cannot be
constructed or reasoned about. -/
structure SlotState where
  poisoned : Bool
  hasWaiters : Bool
  publishedRow : Nat
  rowLtCap : publishedRow < slotRowCap

/-- Helper constructing `some SlotState` iff `Nat.blt publishedRow slotRowCap`
is `true`, avoiding `Classical.choice` or `dite`. -/
@[expose] def mkSlotStateAux (poisoned hasWaiters : Bool) (publishedRow : Nat) :
    ∀ (b : Bool), Nat.blt publishedRow slotRowCap = b → Option SlotState
  | true, h =>
    some ⟨poisoned, hasWaiters, publishedRow, Nat.le_of_ble_eq_true h⟩
  | false, _ => none

/-- Checked `SlotState` constructor: rejects `publishedRow ≥ slotRowCap` with
`none`. -/
@[expose] def mkSlotState? (poisoned hasWaiters : Bool)
    (publishedRow : Nat) : Option SlotState :=
  mkSlotStateAux poisoned hasWaiters publishedRow
    (Nat.blt publishedRow slotRowCap) rfl

private theorem mkSlotStateAux_true (p w : Bool) (row : Nat)
    (b : Bool) (hb : b = true)
    (hEq : Nat.blt row slotRowCap = b) (hLt : row < slotRowCap) :
    mkSlotStateAux p w row b hEq = some ⟨p, w, row, hLt⟩ := by
  cases hb
  rfl

private theorem mkSlotStateAux_false (p w : Bool) (row : Nat)
    (b : Bool) (hb : b = false)
    (hEq : Nat.blt row slotRowCap = b) :
    mkSlotStateAux p w row b hEq = none := by
  cases hb
  rfl

theorem mkSlotState?_of_lt (poisoned hasWaiters : Bool) {row : Nat}
    (hLt : row < slotRowCap) :
    mkSlotState? poisoned hasWaiters row =
      some ⟨poisoned, hasWaiters, row, hLt⟩ :=
  mkSlotStateAux_true poisoned hasWaiters row
    (Nat.blt row slotRowCap) (Nat.ble_eq_true_of_le hLt) rfl hLt

theorem mkSlotState?_of_ge (poisoned hasWaiters : Bool) {row : Nat}
    (hGe : slotRowCap ≤ row) :
    mkSlotState? poisoned hasWaiters row = none := by
  have hFalse : Nat.blt row slotRowCap = false := by
    cases hB : Nat.blt row slotRowCap with
    | false => rfl
    | true =>
      exact False.elim (Nat.not_le_of_lt (Nat.le_of_ble_eq_true hB) hGe)
  exact mkSlotStateAux_false poisoned hasWaiters row
    (Nat.blt row slotRowCap) hFalse rfl

/-- Total `Bool`-selected offset helper reducing definitionally on `Bool`
constructors without `ite` boolean-equality goals. -/
@[expose] def boolWeight (b : Bool) (w : Nat) : Nat :=
  match b with
  | false => 0
  | true => w

private theorem boolWeight_le (b : Bool) (w : Nat) : boolWeight b w ≤ w := by
  cases b with
  | false => exact Nat.zero_le w
  | true => exact Nat.le_refl w

/-- Pack validated `(poisoned : 1, hasWaiters : 1, publishedRow : 30)` into a
32-bit word represented as `Nat`. -/
@[expose] def packSlotWord (s : SlotState) : Nat :=
  boolWeight s.poisoned slotPoisonBit +
  boolWeight s.hasWaiters slotWaitersBit +
  s.publishedRow

/-- Checked 32-bit slot packer: rejects `publishedRow ≥ slotRowCap` with `none`
and packs validated states via `packSlotWord`. -/
@[expose] def packSlotWord? (poisoned hasWaiters : Bool)
    (publishedRow : Nat) : Option Nat :=
  match mkSlotState? poisoned hasWaiters publishedRow with
  | some s => some (packSlotWord s)
  | none => none

theorem packSlotWord?_of_lt (poisoned hasWaiters : Bool) {row : Nat}
    (hLt : row < slotRowCap) :
    packSlotWord? poisoned hasWaiters row =
      some (packSlotWord ⟨poisoned, hasWaiters, row, hLt⟩) := by
  dsimp only [packSlotWord?]
  rw [mkSlotState?_of_lt poisoned hasWaiters hLt]

theorem packSlotWord?_of_ge (poisoned hasWaiters : Bool) {row : Nat}
    (hGe : slotRowCap ≤ row) :
    packSlotWord? poisoned hasWaiters row = none := by
  dsimp only [packSlotWord?]
  rw [mkSlotState?_of_ge poisoned hasWaiters hGe]

/-- Every packed `SlotState` fits strictly inside a 32-bit unsigned word
(`< 2^32`). -/
theorem packSlotWord_lt_wordCap (s : SlotState) :
    packSlotWord s < slotWordCap := by
  have hFlags :
      boolWeight s.poisoned slotPoisonBit +
        boolWeight s.hasWaiters slotWaitersBit ≤
      slotPoisonBit + slotWaitersBit :=
    Nat.add_le_add (boolWeight_le s.poisoned slotPoisonBit)
      (boolWeight_le s.hasWaiters slotWaitersBit)
  have hSumLt :
      boolWeight s.poisoned slotPoisonBit +
        boolWeight s.hasWaiters slotWaitersBit + s.publishedRow <
      slotPoisonBit + slotWaitersBit + slotRowCap :=
    Nat.lt_of_le_of_lt
      (Nat.add_le_add_right hFlags s.publishedRow)
      (Nat.add_lt_add_left s.rowLtCap (slotPoisonBit + slotWaitersBit))
  exact Nat.lt_of_lt_of_le hSumLt slotAllFlags_add_cap_le_wordCap

/-- Unpack `(poisoned : 1, hasWaiters : 1, publishedRow : 30)` from a 32-bit
word represented as `Nat`. -/
@[expose] def unpackSlotWord (w : Nat) : SlotState :=
  { poisoned := !Nat.beq (Nat.mod (Nat.div w slotPoisonBit) 2) 0
    hasWaiters := !Nat.beq (Nat.mod (Nat.div w slotWaitersBit) 2) 0
    publishedRow := Nat.mod w slotRowCap
    rowLtCap := Nat.mod_lt w slotRowCap_pos }

private theorem euclid_quot_eq {m q1 r1 q2 r2 : Nat}
    (hr1 : r1 < m) (hr2 : r2 < m) (hEq : m * q1 + r1 = m * q2 + r2) :
    q1 = q2 := by
  have noLess : ∀ a b ra rb : Nat, ra < m → rb < m →
      m * a + ra = m * b + rb → a < b → False := by
    intro a b ra rb hra _ hSum hLt
    have hSucc : m * (a + 1) ≤ m * b := Nat.mul_le_mul_left m hLt
    have hStep : m * a + m ≤ m * b := by
      have hMul : m * (a + 1) = m * a + m * 1 := Nat.mul_add m a 1
      rw [Nat.mul_one] at hMul
      rw [← hMul]
      exact hSucc
    have hLtSide : m * a + ra < m * a + m := Nat.add_lt_add_left hra (m * a)
    have hRight : m * b ≤ m * b + rb := Nat.le_add_right (m * b) rb
    have hCon : m * a + ra < m * b + rb :=
      Nat.lt_of_lt_of_le hLtSide (Nat.le_trans hStep hRight)
    rw [hSum] at hCon
    exact Nat.lt_irrefl (m * b + rb) hCon
  cases Nat.lt_or_ge q1 q2 with
  | inl h12 => exact False.elim (noLess q1 q2 r1 r2 hr1 hr2 hEq h12)
  | inr h21 =>
    cases Nat.lt_or_eq_of_le h21 with
    | inl hLt21 =>
      exact False.elim (noLess q2 q1 r2 r1 hr2 hr1 hEq.symm hLt21)
    | inr heq => exact heq.symm

private theorem nat_div_mul_add {m q r : Nat} (hm : 0 < m) (hr : r < m) :
    Nat.div (m * q + r) m = q :=
  euclid_quot_eq (Nat.mod_lt (m * q + r) hm) hr
    (Nat.div_add_mod (m * q + r) m)

private theorem nat_mod_mul_add {m q r : Nat} (hm : 0 < m) (hr : r < m) :
    Nat.mod (m * q + r) m = r := by
  have hDecomp : m * Nat.div (m * q + r) m + Nat.mod (m * q + r) m = m * q + r :=
    Nat.div_add_mod (m * q + r) m
  rw [nat_div_mul_add hm hr] at hDecomp
  exact Nat.add_left_cancel hDecomp

private theorem packSlotWord_unfold (p w : Bool) (row : Nat)
    (hRow : row < slotRowCap) :
    packSlotWord ⟨p, w, row, hRow⟩ =
      boolWeight p slotPoisonBit + boolWeight w slotWaitersBit + row := rfl

private theorem slotState_ext {p1 p2 w1 w2 : Bool} {r1 r2 : Nat}
    {h1 : r1 < slotRowCap} {h2 : r2 < slotRowCap}
    (hp : p1 = p2) (hw : w1 = w2) (hr : r1 = r2) :
    (⟨p1, w1, r1, h1⟩ : SlotState) = ⟨p2, w2, r2, h2⟩ := by
  cases hp
  cases hw
  cases hr
  rfl

private theorem unpackSlotWord_mk (word : Nat) (p w : Bool) (r : Nat)
    (hLt : r < slotRowCap)
    (hp : (!Nat.beq (Nat.mod (Nat.div word slotPoisonBit) 2) 0) = p)
    (hw : (!Nat.beq (Nat.mod (Nat.div word slotWaitersBit) 2) 0) = w)
    (hr : Nat.mod word slotRowCap = r) :
    unpackSlotWord word = ⟨p, w, r, hLt⟩ :=
  slotState_ext hp hw hr

/-- Unconditional pack/unpack round-trip for every `s : SlotState`. -/
theorem unpack_packSlotWord (s : SlotState) :
    unpackSlotWord (packSlotWord s) = s := by
  cases s with
  | mk pois wait row hRow =>
    have hModRow : Nat.mod row slotRowCap = row := Nat.mod_eq_of_lt hRow
    have hRowLtP : row < slotPoisonBit :=
      Nat.lt_of_lt_of_le hRow slotRowCap_le_slotPoisonBit
    cases pois <;> cases wait
    · have hPack : packSlotWord ⟨false, false, row, hRow⟩ = row := by
        rw [packSlotWord_unfold]
        dsimp only [boolWeight]
        rw [Nat.zero_add]
      have hDivP : Nat.div row slotPoisonBit = 0 := Nat.div_eq_of_lt hRowLtP
      have hDivW : Nat.div row slotWaitersBit = 0 := Nat.div_eq_of_lt hRow
      rw [hPack]
      exact unpackSlotWord_mk row false false row hRow
        (by rw [hDivP]; rfl)
        (by rw [hDivW]; rfl)
        hModRow
    · have hPack :
          packSlotWord ⟨false, true, row, hRow⟩ = slotWaitersBit * 1 + row := by
        rw [packSlotWord_unfold]
        dsimp only [boolWeight]
        rw [Nat.zero_add, Nat.mul_one]
      have hSumLtP : slotWaitersBit * 1 + row < slotPoisonBit := by
        rw [Nat.mul_one]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hRow slotWaitersBit)
          slotWaiters_add_cap_le_poison
      have hDivP : Nat.div (slotWaitersBit * 1 + row) slotPoisonBit = 0 :=
        Nat.div_eq_of_lt hSumLtP
      have hDivW : Nat.div (slotWaitersBit * 1 + row) slotWaitersBit = 1 :=
        nat_div_mul_add slotRowCap_pos hRow
      have hModW : Nat.mod (slotWaitersBit * 1 + row) slotRowCap = row :=
        nat_mod_mul_add slotRowCap_pos hRow
      rw [hPack]
      exact unpackSlotWord_mk _ false true row hRow
        (by rw [hDivP]; rfl)
        (by rw [hDivW]; rfl)
        hModW
    · have hPackP :
          packSlotWord ⟨true, false, row, hRow⟩ = slotPoisonBit * 1 + row := by
        rw [packSlotWord_unfold]
        dsimp only [boolWeight]
        rw [Nat.add_zero, Nat.mul_one]
      have hPackW :
          packSlotWord ⟨true, false, row, hRow⟩ = slotWaitersBit * 2 + row := by
        rw [packSlotWord_unfold]
        dsimp only [boolWeight]
        rfl
      have hDivP : Nat.div (slotPoisonBit * 1 + row) slotPoisonBit = 1 :=
        nat_div_mul_add slotPoisonBit_pos hRowLtP
      have hDivW : Nat.div (slotWaitersBit * 2 + row) slotWaitersBit = 2 :=
        nat_div_mul_add slotRowCap_pos hRow
      have hModW : Nat.mod (slotWaitersBit * 2 + row) slotRowCap = row :=
        nat_mod_mul_add slotRowCap_pos hRow
      exact unpackSlotWord_mk _ true false row hRow
        (by rw [hPackP, hDivP]; rfl)
        (by rw [hPackW, hDivW]; rfl)
        (by rw [hPackW, hModW])
    · have hPackP :
          packSlotWord ⟨true, true, row, hRow⟩ =
            slotPoisonBit * 1 + (slotWaitersBit + row) := by
        rw [packSlotWord_unfold]
        dsimp only [boolWeight]
        rw [Nat.mul_one, Nat.add_assoc]
      have hSmall : slotWaitersBit + row < slotPoisonBit :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hRow slotWaitersBit)
          slotWaiters_add_cap_le_poison
      have hDivP :
          Nat.div (slotPoisonBit * 1 + (slotWaitersBit + row)) slotPoisonBit = 1 :=
        nat_div_mul_add slotPoisonBit_pos hSmall
      have hPackW :
          packSlotWord ⟨true, true, row, hRow⟩ = slotWaitersBit * 3 + row := by
        rw [packSlotWord_unfold]
        dsimp only [boolWeight]
        have hEq : slotPoisonBit + slotWaitersBit = slotWaitersBit * 3 := rfl
        rw [hEq]
      have hDivW : Nat.div (slotWaitersBit * 3 + row) slotWaitersBit = 3 :=
        nat_div_mul_add slotRowCap_pos hRow
      have hModPW : Nat.mod (slotWaitersBit * 3 + row) slotRowCap = row :=
        nat_mod_mul_add slotRowCap_pos hRow
      exact unpackSlotWord_mk _ true true row hRow
        (by rw [hPackP, hDivP]; rfl)
        (by rw [hPackW, hDivW]; rfl)
        (by rw [hPackW, hModPW])

/-- Data-monotonicity preorder on `SlotState`: `publishedRow` is non-decreasing
and `poisoned = true` is absorbing, while `hasWaiters` is unconstrained so
threads can register/clear futex waiters non-monotonically. -/
@[expose] def SlotStateLe (s₁ s₂ : SlotState) : Prop :=
  s₁.publishedRow ≤ s₂.publishedRow ∧ (s₁.poisoned = true → s₂.poisoned = true)

theorem slotStateLe_refl (s : SlotState) : SlotStateLe s s :=
  ⟨Nat.le_refl s.publishedRow, fun h => h⟩

theorem slotStateLe_trans {s₁ s₂ s₃ : SlotState}
    (h12 : SlotStateLe s₁ s₂) (h23 : SlotStateLe s₂ s₃) :
    SlotStateLe s₁ s₃ :=
  ⟨Nat.le_trans h12.1 h23.1, fun hp => h23.2 (h12.2 hp)⟩

/-- Persistent consumer readiness witness: once `publishedRow ≥ needed` or the
slot is poisoned, no future monotonic publication can revoke readiness. -/
@[expose] def RowPrefixReady (needed : Nat) (s : SlotState) : Prop :=
  s.poisoned = true ∨ needed ≤ s.publishedRow

theorem rowPrefixReady_mono {needed : Nat} {s₁ s₂ : SlotState}
    (hLe : SlotStateLe s₁ s₂) (hReady : RowPrefixReady needed s₁) :
    RowPrefixReady needed s₂ :=
  match hReady with
  | Or.inl hp => Or.inl (hLe.2 hp)
  | Or.inr hr => Or.inr (Nat.le_trans hr hLe.1)

/-- Poison-or-completion wait-exit theorem: whenever a producer's terminal state
`sEnd` is either poisoned or reaches `hRef`, every valid edge-clamped row
demand (`needed ≤ hRef`) achieves `RowPrefixReady needed sEnd`. -/
theorem terminal_satisfies_edge_clamped_wait {hRef needed : Nat}
    (hBound : needed ≤ hRef) {sEnd : SlotState}
    (hTerm : sEnd.poisoned = true ∨ sEnd.publishedRow = hRef) :
    RowPrefixReady needed sEnd :=
  match hTerm with
  | Or.inl hp => Or.inl hp
  | Or.inr hr => Or.inr (by rw [hr]; exact hBound)

/-! ## Part III: Constructive Multi-Predecessor Scoreboard DAG Liveness -/

/-- Finite static task dependency DAG with an integer topological rank. -/
structure ScoreboardDag where
  numTasks : Nat
  rank : Nat → Nat
  deps : Nat → List Nat

/-- Every dependency `v ∈ d.deps u` of an in-bounds task `u < d.numTasks` is
in-bounds and has strictly smaller rank (`d.rank v < d.rank u`). -/
@[expose] def ValidDagRank (d : ScoreboardDag) : Prop :=
  ∀ u v : Nat, u < d.numTasks → v ∈ d.deps u → v < d.numTasks ∧ d.rank v < d.rank u

/-- Helper selecting between a candidate task `cand` and the current best task
`best` by minimal `rank` (`Nat.blt (rank best) (rank cand)`). -/
@[expose] def minRankPick (rank : Nat → Nat) (cand : Nat) :
    Option Nat → Option Nat
  | none => some cand
  | some best => if Nat.blt (rank best) (rank cand) then some best else some cand

/-- Constructive minimal-rank unfinished task search across `0 ..< limit`
(`0` `Classical.choice`, `0` `._unsafe_rec` via `@Nat.rec`). -/
@[expose] def findMinRankBelow (rank : Nat → Nat) (done : Nat → Bool)
    (limit : Nat) : Option Nat :=
  @Nat.rec (fun _ => Option Nat)
    none
    (fun k prev => if done k then prev else minRankPick rank k prev)
    limit

private theorem minRankPick_lt {rank : Nat → Nat} {cand limit : Nat}
    {prev : Option Nat} {u : Nat}
    (hCand : cand < limit)
    (hPrev : ∀ p : Nat, prev = some p → p < limit)
    (hEq : minRankPick rank cand prev = some u) : u < limit := by
  cases prev with
  | none =>
    dsimp only [minRankPick] at hEq
    have hCu := Option.some.inj hEq
    rw [← hCu]
    exact hCand
  | some best =>
    dsimp only [minRankPick] at hEq
    cases hBlt : Nat.blt (rank best) (rank cand) with
    | true =>
      rw [hBlt] at hEq
      have hBu := Option.some.inj hEq
      rw [← hBu]
      exact hPrev best rfl
    | false =>
      rw [hBlt] at hEq
      have hCu := Option.some.inj hEq
      rw [← hCu]
      exact hCand

theorem findMinRankBelow_lt (rank : Nat → Nat) (done : Nat → Bool) :
    ∀ (limit u : Nat), findMinRankBelow rank done limit = some u → u < limit
  | 0, _, h => by nomatch h
  | n + 1, u, h => by
    dsimp only [findMinRankBelow] at h
    cases hDone : done n with
    | true =>
      rw [hDone] at h
      exact Nat.lt_succ_of_lt (findMinRankBelow_lt rank done n u h)
    | false =>
      rw [hDone] at h
      exact minRankPick_lt (Nat.lt_succ_self n)
        (fun p hp => Nat.lt_succ_of_lt (findMinRankBelow_lt rank done n p hp)) h

private theorem minRankPick_unfinished {rank : Nat → Nat} {done : Nat → Bool}
    {cand : Nat} {prev : Option Nat} {u : Nat}
    (hCand : done cand = false)
    (hPrev : ∀ p : Nat, prev = some p → done p = false)
    (hEq : minRankPick rank cand prev = some u) : done u = false := by
  cases prev with
  | none =>
    dsimp only [minRankPick] at hEq
    have hCu := Option.some.inj hEq
    rw [← hCu]
    exact hCand
  | some best =>
    dsimp only [minRankPick] at hEq
    cases hBlt : Nat.blt (rank best) (rank cand) with
    | true =>
      rw [hBlt] at hEq
      have hBu := Option.some.inj hEq
      rw [← hBu]
      exact hPrev best rfl
    | false =>
      rw [hBlt] at hEq
      have hCu := Option.some.inj hEq
      rw [← hCu]
      exact hCand

theorem findMinRankBelow_unfinished (rank : Nat → Nat) (done : Nat → Bool) :
    ∀ (limit u : Nat),
      findMinRankBelow rank done limit = some u → done u = false
  | 0, _, h => by nomatch h
  | n + 1, u, h => by
    dsimp only [findMinRankBelow] at h
    cases hDone : done n with
    | true =>
      rw [hDone] at h
      exact findMinRankBelow_unfinished rank done n u h
    | false =>
      rw [hDone] at h
      exact minRankPick_unfinished hDone (findMinRankBelow_unfinished rank done n) h

private theorem findMinRankBelow_succ (rank : Nat → Nat) (done : Nat → Bool)
    (n : Nat) :
    findMinRankBelow rank done (n + 1) =
      if done n then findMinRankBelow rank done n
      else minRankPick rank n (findMinRankBelow rank done n) := rfl

theorem findMinRankBelow_some_of_exists (rank : Nat → Nat) (done : Nat → Bool) :
    ∀ (limit k : Nat), k < limit → done k = false →
      ∃ u : Nat, findMinRankBelow rank done limit = some u
  | 0, k, hk, _ => False.elim (Nat.not_lt_zero k hk)
  | n + 1, k, hk, hDk => by
    rw [findMinRankBelow_succ]
    cases hDn : done n with
    | false =>
      cases hPrev : findMinRankBelow rank done n with
      | none => exact ⟨n, by dsimp only [minRankPick]; rfl⟩
      | some best =>
        dsimp only [minRankPick]
        cases Nat.blt (rank best) (rank n) with
        | true => exact ⟨best, rfl⟩
        | false => exact ⟨n, rfl⟩
    | true =>
      have hkLt : k < n := by
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
        | inl hlt => exact hlt
        | inr heq =>
          rw [heq, hDn] at hDk
          exact False.elim (Bool.noConfusion hDk)
      exact findMinRankBelow_some_of_exists rank done n k hkLt hDk

theorem findMinRankBelow_minimal (rank : Nat → Nat) (done : Nat → Bool) :
    ∀ (limit u v : Nat),
      findMinRankBelow rank done limit = some u →
      v < limit → done v = false → rank u ≤ rank v
  | 0, _, v, h, _, _ => by nomatch h
  | n + 1, u, v, h, hv, hDv => by
    rw [findMinRankBelow_succ] at h
    cases hDn : done n with
    | true =>
      rw [hDn] at h
      have hvLt : v < n := by
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with
        | inl hlt => exact hlt
        | inr heq =>
          rw [heq, hDn] at hDv
          exact False.elim (Bool.noConfusion hDv)
      exact findMinRankBelow_minimal rank done n u v h hvLt hDv
    | false =>
      rw [hDn] at h
      cases hPrev : findMinRankBelow rank done n with
      | none =>
        rw [hPrev] at h
        dsimp only [minRankPick] at h
        have hNu : n = u := Option.some.inj h
        rw [← hNu]
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with
        | inl hlt =>
          have hSome := findMinRankBelow_some_of_exists rank done n v hlt hDv
          cases hSome with
          | intro w hw =>
            rw [hPrev] at hw
            nomatch hw
        | inr heq =>
          rw [heq]
          exact Nat.le_refl (rank n)
      | some best =>
        rw [hPrev] at h
        dsimp only [minRankPick] at h
        cases hBlt : Nat.blt (rank best) (rank n) with
        | true =>
          rw [hBlt] at h
          have hBu : best = u := Option.some.inj h
          have hBestLtN : rank best < rank n := Nat.le_of_ble_eq_true hBlt
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with
          | inl hlt =>
            rw [← hBu]
            exact findMinRankBelow_minimal rank done n best v hPrev hlt hDv
          | inr heq =>
            rw [heq, ← hBu]
            exact Nat.le_of_lt hBestLtN
        | false =>
          rw [hBlt] at h
          have hNu : n = u := Option.some.inj h
          have hNLeBest : rank n ≤ rank best := by
            cases Nat.lt_or_ge (rank best) (rank n) with
            | inl hLt =>
              have hBt : Nat.blt (rank best) (rank n) = true :=
                Nat.ble_eq_true_of_le hLt
              rw [hBlt] at hBt
              exact False.elim (Bool.noConfusion hBt)
            | inr hGe => exact hGe
          rw [← hNu]
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with
          | inl hlt =>
            exact Nat.le_trans hNLeBest
              (findMinRankBelow_minimal rank done n best v hPrev hlt hDv)
          | inr heq =>
            rw [heq]
            exact Nat.le_refl (rank n)

/-- A task `u` is ready to execute when `u < d.numTasks`, `done u = false`, and
every dependency `v ∈ d.deps u` already has `done v = true`. -/
@[expose] def TaskReady (d : ScoreboardDag) (done : Nat → Bool) (u : Nat) : Prop :=
  u < d.numTasks ∧ done u = false ∧ ∀ v : Nat, v ∈ d.deps u → done v = true

/-- Total constructive scoreboard deadlock-freedom theorem (`[]` zero axioms,
`0` `Classical.choice`): for any valid static DAG `d` and any boolean completion
vector `done`, if any task `k < d.numTasks` remains unfinished,
`findMinRankBelow d.rank done d.numTasks` deterministically returns an enabled
task `u` whose dependencies are all already finished. -/
theorem scoreboard_progress_witness (d : ScoreboardDag) (done : Nat → Bool)
    (hValid : ValidDagRank d) {k : Nat} (hk : k < d.numTasks)
    (hNotDone : done k = false) :
    ∃ u : Nat, findMinRankBelow d.rank done d.numTasks = some u ∧
      TaskReady d done u := by
  have hEx := findMinRankBelow_some_of_exists d.rank done d.numTasks k hk hNotDone
  cases hEx with
  | intro u hu =>
    refine ⟨u, hu, findMinRankBelow_lt d.rank done d.numTasks u hu,
      findMinRankBelow_unfinished d.rank done d.numTasks u hu, ?_⟩
    intro v hvMem
    have hDep := hValid u v (findMinRankBelow_lt d.rank done d.numTasks u hu) hvMem
    cases hDv : done v with
    | true => rfl
    | false =>
      have hMin :=
        findMinRankBelow_minimal d.rank done d.numTasks u v hu hDep.1 hDv
      exact False.elim (Nat.not_le_of_lt hDep.2 hMin)

/-! ## Part IV: Concrete HEVC/AV1 WPP and 10-Stage VVC CTU Scoreboard Ranks -/

/-- WPP CTU rank (`rx + 2 * ry`): strictly decreases for both left neighbor
`(rx - 1, ry)` and top-right WPP neighbor `(rx + 1, ry - 1)`. -/
@[expose] def wppRank (rx ry : Nat) : Nat := rx + 2 * ry

theorem wppRank_left_lt {rx ry : Nat} (hx : 0 < rx) :
    wppRank (rx - 1) ry < wppRank rx ry := by
  dsimp only [wppRank]
  have hxEq : rx - 1 + 1 = rx := Nat.sub_add_cancel hx
  have hL : rx - 1 + 2 * ry + 1 = rx + 2 * ry := by
    rw [Nat.add_assoc (rx - 1) (2 * ry) 1, Nat.add_comm (2 * ry) 1,
        ← Nat.add_assoc (rx - 1) 1 (2 * ry), hxEq]
  rw [← hL]
  exact Nat.lt_succ_self _

theorem wppRank_topRight_lt {rx ry : Nat} (hy : 0 < ry) :
    wppRank (rx + 1) (ry - 1) < wppRank rx ry := by
  dsimp only [wppRank]
  have hyEq : ry - 1 + 1 = ry := Nat.sub_add_cancel hy
  have hMul : 2 * (ry - 1) + 2 = 2 * ry := by
    have h1 : 2 * (ry - 1) + 2 = 2 * (ry - 1 + 1) :=
      (Nat.mul_add 2 (ry - 1) 1).symm
    rw [h1, hyEq]
  have hSum : (rx + 1) + 2 * (ry - 1) + 1 = rx + 2 * ry := by
    have hA : (rx + 1) + 2 * (ry - 1) + 1 = rx + (1 + (2 * (ry - 1) + 1)) := by
      rw [Nat.add_assoc, Nat.add_assoc]
    have hB : rx + (1 + (2 * (ry - 1) + 1)) = rx + (2 * (ry - 1) + 2) := by
      rw [Nat.add_comm 1 (2 * (ry - 1) + 1), Nat.add_assoc (2 * (ry - 1)) 1 1]
    rw [hA, hB, hMul]
  rw [← hSum]
  exact Nat.lt_succ_self _

/-- Multi-stage VVC CTU rank (`stage * 4 + rx + 2 * ry`): preserves both
intra-stage WPP dependencies (`left` and `top-right`) AND arbitrary inter-stage
backward-halo dependencies across the entire `3x3` Moore neighborhood
`(dx, dy ∈ {-1, 0, +1})` (including `(rx + 1, ry + 1)` from any earlier stage
`stage' < stage`). -/
@[expose] def vvcCtuRank (rx ry stage : Nat) : Nat :=
  stage * 4 + wppRank rx ry

theorem vvcCtuRank_intra_left_lt {rx ry stage : Nat} (hx : 0 < rx) :
    vvcCtuRank (rx - 1) ry stage < vvcCtuRank rx ry stage :=
  Nat.add_lt_add_left (wppRank_left_lt hx) (stage * 4)

theorem vvcCtuRank_intra_topRight_lt {rx ry stage : Nat} (hy : 0 < ry) :
    vvcCtuRank (rx + 1) (ry - 1) stage < vvcCtuRank rx ry stage :=
  Nat.add_lt_add_left (wppRank_topRight_lt hy) (stage * 4)

theorem vvcCtuRank_prevStage_mooreHalo_lt
    {rx ry stage rx' ry' stage' : Nat}
    (hs : stage' < stage) (hx : rx' ≤ rx + 1) (hy : ry' ≤ ry + 1) :
    vvcCtuRank rx' ry' stage' < vvcCtuRank rx ry stage := by
  dsimp only [vvcCtuRank, wppRank]
  have hy2 : 2 * ry' ≤ 2 * ry + 2 := by
    have hMul : 2 * ry' ≤ 2 * (ry + 1) := Nat.mul_le_mul_left 2 hy
    have hEq : 2 * (ry + 1) = 2 * ry + 2 := Nat.mul_add 2 ry 1
    rw [hEq] at hMul
    exact hMul
  have hWpp : rx' + 2 * ry' + 1 ≤ (rx + 2 * ry) + 4 := by
    have h1 : rx' + 2 * ry' ≤ (rx + 1) + (2 * ry + 2) := Nat.add_le_add hx hy2
    have h2 : (rx + 1) + (2 * ry + 2) + 1 = (rx + 2 * ry) + 4 := by
      rw [Nat.add_assoc rx 1 (2 * ry + 2),
          Nat.add_comm 1 (2 * ry + 2),
          Nat.add_assoc (2 * ry) 2 1,
          ← Nat.add_assoc rx (2 * ry) (2 + 1),
          Nat.add_assoc (rx + 2 * ry) (2 + 1) 1]
    exact Nat.le_trans (Nat.add_le_add_right h1 1) (Nat.le_of_eq h2)
  have hStage : (stage' + 1) * 4 ≤ stage * 4 :=
    Nat.mul_le_mul_right 4 hs
  have hStep1 :
      stage' * 4 + (rx' + 2 * ry') + 1 ≤ stage' * 4 + ((rx + 2 * ry) + 4) := by
    rw [Nat.add_assoc (stage' * 4) (rx' + 2 * ry') 1]
    exact Nat.add_le_add_left hWpp (stage' * 4)
  have hEqStep :
      stage' * 4 + ((rx + 2 * ry) + 4) = (stage' + 1) * 4 + (rx + 2 * ry) := by
    rw [Nat.add_comm (rx + 2 * ry) 4, ← Nat.add_assoc (stage' * 4) 4 (rx + 2 * ry),
        ← Nat.succ_mul stage' 4]
  rw [hEqStep] at hStep1
  exact Nat.le_trans hStep1 (Nat.add_le_add_right hStage (rx + 2 * ry))

end Anneal.WavefrontReclaim

end
