-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Array.Basic
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.MemAlloc
import Anneal.MirCorrespondence.LayoutAndAlign

/-!
# Upstream `Miri.Memory` Byte-Slice, Tracked Memory, and Pointer Laws

Companion module to `Anneal.MirCorrespondence.LayoutAndAlign` establishing
upstream-only correspondence lemmas between `Trusted.MirSemantics` and
`Miri.Memory`:

1. **Upstream `Miri.Memory` Byte-Slice & Provenance Laws** (Section 4):
   - Non-overflowing `AllocRange.{endExclusive, subrange}` laws.
   - Lazy `InitMask.{isRangeInitialized, setRange}` laws on `InitMask.new`
     (proved directly from upstream definitions without patched vendor lemmas).
   - `ProvenanceMap.{rangeEmpty, clear, insertPtr}` round-trip laws on
     `ProvenanceMap.new`.
   - `Miri.Memory.Allocation.{fromBytes, getBytesUnchecked,
     getBytesStripProvenance, writeBytes}` specifications including read-only
     `.Not` rejection.
2. **Tracked Slice & `CallerMemory` Simulation over `Miri.Memory.MemoryState`**
   (Section 5):
   - `AllocByteSliceRel`, `TrackedSliceMemRel` (scoped to an explicit `tracked`
     list of slice IDs against Miri's real `Miri.Memory.MemoryState`), and
     `CallerMemorySliceRel` (bridging `State.callerMem : CallerMemory`).
   - Preservation of `TrackedSliceMemRel` across `allocateStack` (which appends
     `.uninit` stack bytes outside `tracked`), `writeBytes`/`storeIndirect` on
     untracked stack slots, `deallocateStack` on untracked stack slots, and
     lockstep `writeBytes` + `MemoryState.setLiveAllocation` on mutable tracked
     slices.
3. **64-Bit Pointer Offsets, `checkedBounds`, `checkAndDerefPtr` & Provenance**
   (Section 6):
   - 64-bit `PointerArithmetic` and provenance-preserving wrapping offsets.
   - Non-negative and negative `checkedBounds` in-bounds, out-of-bounds, and
     outside-`i64` error laws.
   - `checkAndDerefPtr` live, dangling-integer, and dead-allocation error laws
     (paired with `MemoryState.getAllocInfo` on dead entries and
     `deallocateStack_spec`).
   - Full 64-bit `Allocation.writePointer` -> `Allocation.readScalar` provenance
     round-trip.
4. **Concrete End-to-End Non-Vacuity Witnesses** (Section 7):
   - Four concrete witnesses covering Miri zero-size pointer alignment
     agreeing with `MirSemantics.readBytes` at `size = 0`, coexistence of
     tracked caller slices with uninitialized/live/dead stack allocations in
     `MemoryState`, indirect stack use-after-free, and 64-bit pointer offset +
     bounds + provenance.
-/

namespace Anneal.MirCorrespondence

open Trusted
open Trusted.MirAst
open Trusted.MirSemantics
open Miri.ABI
open Miri.Memory

/-! ## Section 4: Upstream `Miri.Memory` Byte-Slice & Provenance Laws -/

/-- Exact non-overflowing specification of `AllocRange.endExclusive`. -/
theorem allocRange_endExclusive_of_lt (range : AllocRange)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64) :
    range.endExclusive =
      .ok (Size.ofBytes (UInt64.ofNat
        (range.start.bytes.toNat + range.size.bytes.toNat))) := by
  dsimp only [AllocRange.endExclusive, AllocRange.end, Size.add,
    Except.mapError]
  have h_add : (range.start.bytes + range.size.bytes).toNat =
      range.start.bytes.toNat + range.size.bytes.toNat :=
    u64_add_toNat_of_lt h_lt
  have h_nlt :
      ¬ (range.start.bytes + range.size.bytes < range.start.bytes) :=
    u64_not_lt_of_le (by rw [h_add]; exact Nat.le_add_right _ _)
  rw [ite_neg_eq h_nlt]
  apply congrArg Except.ok
  apply congrArg Size.ofBytes
  exact u64_eq_of_toNat_eq (h_add.trans (u64_ofNat_toNat_of_lt h_lt).symm)

/-- Exact specification of `AllocRange.subrange` agreeing with interval
containment (`subStart + subSize ≤ outerSize`). -/
theorem allocRange_subrange_of_inbounds (outer sub : AllocRange)
    (h_outer :
      outer.start.bytes.toNat + outer.size.bytes.toNat < Nat.pow 2 64)
    (h_in :
      sub.start.bytes.toNat + sub.size.bytes.toNat ≤
        outer.size.bytes.toNat) :
    outer.subrange sub =
      .ok (allocRange
        (Size.ofBytes (UInt64.ofNat
          (outer.start.bytes.toNat + sub.start.bytes.toNat)))
        sub.size) := by
  have h_sub_start_lt :
      outer.start.bytes.toNat + sub.start.bytes.toNat < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) h_in) _)
      h_outer
  have h_res_end_le :
      (outer.start.bytes.toNat + sub.start.bytes.toNat) +
          sub.size.bytes.toNat ≤
        outer.start.bytes.toNat + outer.size.bytes.toNat := by
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left h_in _
  have h_res_end_lt :
      (outer.start.bytes.toNat + sub.start.bytes.toNat) +
          sub.size.bytes.toNat < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt h_res_end_le h_outer
  dsimp only [AllocRange.subrange, bind, Bind.bind, Except.bind, pure,
    Pure.pure, Except.pure]
  have h_sa :
      (Size.add outer.start sub.start).mapError MemoryError.sizeError =
        .ok (Size.ofBytes (UInt64.ofNat
          (outer.start.bytes.toNat + sub.start.bytes.toNat))) :=
    allocRange_endExclusive_of_lt (allocRange outer.start sub.start)
      h_sub_start_lt
  rw [h_sa]
  dsimp only
  let start' := Size.ofBytes
    (UInt64.ofNat (outer.start.bytes.toNat + sub.start.bytes.toNat))
  have h_re := allocRange_endExclusive_of_lt (allocRange start' sub.size)
    (by
      dsimp only [allocRange, start', Size.ofBytes]
      rw [u64_ofNat_toNat_of_lt h_sub_start_lt]
      exact h_res_end_lt)
  rw [h_re]
  dsimp only [allocRange]
  rw [allocRange_endExclusive_of_lt outer h_outer]
  dsimp only
  have h_le :
      (Size.ofBytes (UInt64.ofNat
          (start'.bytes.toNat + sub.size.bytes.toNat))).bytes ≤
        (Size.ofBytes (UInt64.ofNat
          (outer.start.bytes.toNat + outer.size.bytes.toNat))).bytes := by
    apply u64_le_of_toNat_le
    dsimp only [start', Size.ofBytes]
    rw [u64_ofNat_toNat_of_lt h_sub_start_lt,
      u64_ofNat_toNat_of_lt h_res_end_lt, u64_ofNat_toNat_of_lt h_outer]
    exact h_res_end_le
  rw [ite_pos_eq h_le]

/-- Upstream `InitMask.isRangeInitialized` on `InitMask.new len true` succeeds
for every in-bounds range. -/
theorem initMask_lazy_true_isRangeInitialized (len : Size) (range : AllocRange)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64)
    (h_le :
      range.start.bytes.toNat + range.size.bytes.toNat ≤ len.bytes.toNat) :
    (InitMask.new len true).isRangeInitialized range = .ok (.ok ()) := by
  dsimp only [InitMask.isRangeInitialized, InitMask.new, bind, Bind.bind,
    Except.bind, pure, Pure.pure, Except.pure]
  rw [allocRange_endExclusive_of_lt range h_lt]
  dsimp only [Size.ofBytes]
  have h_nlt :
      ¬ (len.bytes <
          UInt64.ofNat (range.start.bytes.toNat + range.size.bytes.toNat)) :=
    u64_not_lt_of_le (by rw [u64_ofNat_toNat_of_lt h_lt]; exact h_le)
  rw [ite_neg_eq h_nlt]
  rfl

/-- Upstream `InitMask.isRangeInitialized` on `InitMask.new len false` reports
`.ok (.error range)` for every in-bounds range. -/
theorem initMask_lazy_false_isRangeInitialized (len : Size) (range : AllocRange)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64)
    (h_le :
      range.start.bytes.toNat + range.size.bytes.toNat ≤ len.bytes.toNat) :
    (InitMask.new len false).isRangeInitialized range =
      .ok (.error range) := by
  dsimp only [InitMask.isRangeInitialized, InitMask.new, bind, Bind.bind,
    Except.bind, pure, Pure.pure, Except.pure]
  rw [allocRange_endExclusive_of_lt range h_lt]
  dsimp only [Size.ofBytes]
  have h_nlt :
      ¬ (len.bytes <
          UInt64.ofNat (range.start.bytes.toNat + range.size.bytes.toNat)) :=
    u64_not_lt_of_le (by rw [u64_ofNat_toNat_of_lt h_lt]; exact h_le)
  rw [ite_neg_eq h_nlt]
  rfl

/-- Upstream `InitMask.setRange` on `InitMask.new len true` (`newState = true`)
leaves an in-bounds mask lazily initialized without materializing blocks. -/
theorem initMask_lazy_true_setRange_true (len : Size) (range : AllocRange)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64)
    (h_le :
      range.start.bytes.toNat + range.size.bytes.toNat ≤ len.bytes.toNat) :
    (InitMask.new len true).setRange range true =
      .ok (InitMask.new len true) := by
  dsimp only [InitMask.setRange, InitMask.new, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure]
  rw [allocRange_endExclusive_of_lt range h_lt]
  dsimp only [Size.ofBytes]
  let endBytes :=
    UInt64.ofNat (range.start.bytes.toNat + range.size.bytes.toNat)
  cases h_full : decide (range.start.bytes = 0 ∧ len.bytes ≤ endBytes) with
  | true =>
    have h_f := of_decide_eq_true h_full
    rw [ite_pos_eq h_f]
    have h_eq_len : endBytes = len.bytes := by
      apply u64_eq_of_toNat_eq
      dsimp only [endBytes]
      rw [u64_ofNat_toNat_of_lt h_lt]
      have h_ge :
          len.bytes.toNat ≤
            range.start.bytes.toNat + range.size.bytes.toNat := by
        have h_u := UInt64.le_iff_toNat_le.1 h_f.2
        dsimp only [endBytes] at h_u
        rw [u64_ofNat_toNat_of_lt h_lt] at h_u
        exact h_u
      exact Nat.le_antisymm h_le h_ge
    dsimp only [endBytes] at h_eq_len
    rw [h_eq_len]
  | false =>
    rw [ite_neg_eq (of_decide_eq_false h_full)]
    have h_nlt : ¬ (len.bytes < endBytes) :=
      u64_not_lt_of_le (by
        dsimp only [endBytes]
        rw [u64_ofNat_toNat_of_lt h_lt]
        exact h_le)
    rw [show (true == true) = true from rfl, ite_true_eq, ite_neg_eq h_nlt]

private def provAdjustedStartMirror (range : AllocRange) (ptrSize : Size) :
    Except ProvenanceMapError Size :=
  if (ptrSize.bytes == 0) = true then
    Except.error ProvenanceMapError.pointerSizeZero
  else
    Except.ok (Size.ofBytes
      (UInt64.ofNat (range.start.bytes.toNat - (ptrSize.bytes.toNat - 1))))

private def provRangeEndMirror (range : AllocRange) :
    Except ProvenanceMapError Size :=
  Except.mapError ProvenanceMapError.memory range.endExclusive

private def provRangePtrsNewMirror {Prov : Type} (range : AllocRange)
    (ptrSize : Size) : Except ProvenanceMapError (Array (Size × Prov)) :=
  Except.bind (provAdjustedStartMirror range ptrSize) fun _ =>
  Except.bind (provRangeEndMirror range) fun _ =>
  Except.ok (Array.mk [])

private theorem provRangePtrs_new_eq_mirror {Prov : Type} (range : AllocRange)
    (ptrSize : Size) :
    (ProvenanceMap.new (Prov := Prov)).rangePtrs range ptrSize =
      provRangePtrsNewMirror range ptrSize := rfl

private def provRangeBytesNewMirror {Prov : Type} (range : AllocRange) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) :=
  Except.bind (provRangeEndMirror range) fun _ =>
  Except.ok (Array.mk [])

private theorem provRangeBytes_new_eq_mirror {Prov : Type}
    (range : AllocRange) :
    (ProvenanceMap.new (Prov := Prov)).rangeBytes range =
      provRangeBytesNewMirror range := rfl

private theorem provRangePtrs_new_ok {Prov : Type} (range : AllocRange)
    (ptrSize : Size) (h_pne : ptrSize.bytes ≠ 0)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64) :
    (ProvenanceMap.new (Prov := Prov)).rangePtrs range ptrSize =
      .ok (Array.mk []) := by
  rw [provRangePtrs_new_eq_mirror]
  dsimp only [provRangePtrsNewMirror, provAdjustedStartMirror,
    provRangeEndMirror]
  have h_pbeq : (ptrSize.bytes == 0) = false := by
    cases h_eq : (ptrSize.bytes == 0) with
    | false => rfl
    | true => exact False.elim (h_pne (eq_of_beq h_eq))
  rw [h_pbeq, ite_false_eq]
  dsimp only [Except.bind]
  rw [allocRange_endExclusive_of_lt range h_lt]
  rfl

/-- Upstream `ProvenanceMap.new` has empty range overlap for every valid
non-overflowing range and nonzero `pointerSize`. -/
theorem provenanceMap_new_rangeEmpty {Prov : Type} (range : AllocRange)
    (ptrSize : Size) (h_pne : ptrSize.bytes ≠ 0)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64) :
    (ProvenanceMap.new (Prov := Prov)).rangeEmpty range ptrSize = .ok true := by
  dsimp only [ProvenanceMap.rangeEmpty, bind, Bind.bind, Except.bind, pure,
    Pure.pure, Except.pure]
  rw [provRangePtrs_new_ok range ptrSize h_pne h_lt]
  dsimp only
  rw [show (!((Array.mk ([] : List (Size × Prov))).isEmpty)) = false from rfl,
    ite_false_eq, provRangeBytes_new_eq_mirror]
  dsimp only [provRangeBytesNewMirror, provRangeEndMirror]
  rw [allocRange_endExclusive_of_lt range h_lt]
  rfl

private def provCheckedMirror {α Prov : Type}
    (r : Except ProvenanceMapError α) : ProvenanceMap.Mutation Prov α :=
  fun s =>
    match r with
    | Except.ok v => EStateM.Result.ok v s
    | Except.error e => EStateM.Result.error e s

/-- Upstream `ProvenanceMap.clear` on `ProvenanceMap.new` is a no-op for every
non-overflowing range and nonzero `pointerSize`. -/
theorem provenanceMap_new_clear {Prov : Type} (range : AllocRange)
    (data : Array UInt8) (ptrSize : Size) (h_pne : ptrSize.bytes ≠ 0)
    (h_lt : range.start.bytes.toNat + range.size.bytes.toNat < Nat.pow 2 64) :
    ProvenanceMap.clear range data ptrSize (ProvenanceMap.new (Prov := Prov)) =
      .ok () (ProvenanceMap.new (Prov := Prov)) := by
  have h_end := allocRange_endExclusive_of_lt range h_lt
  have h_rp := provRangePtrs_new_ok (Prov := Prov) range ptrSize h_pne h_lt
  cases h_sz0 : (range.size.bytes == 0) with
  | true =>
    dsimp only [ProvenanceMap.clear]
    rw [h_sz0, ite_true_eq]
    rfl
  | false =>
    dsimp only [ProvenanceMap.clear, bind, Bind.bind, EStateM.bind, pure,
      Pure.pure, EStateM.pure, EStateM.get, EStateM.set]
    rw [h_sz0, ite_false_eq]
    change
      (EStateM.bind (provCheckedMirror (provRangeEndMirror range)) _
        (ProvenanceMap.new (Prov := Prov))) = _
    dsimp only [provCheckedMirror, provRangeEndMirror]
    rw [h_end]
    dsimp only [Except.mapError, EStateM.bind, EStateM.get, EStateM.set,
      Option.map]
    change
      (EStateM.bind
        (provCheckedMirror
          ((ProvenanceMap.new (Prov := Prov)).rangePtrs range ptrSize)) _
        (ProvenanceMap.new (Prov := Prov))) = _
    rw [h_rp]
    rfl

/-- Upstream `ProvenanceMap.insertPtr` into `ProvenanceMap.new` followed by
`getPtr` and `readPtr` recovers `some prov` verbatim. -/
theorem provenanceMap_new_insertPtr_roundTrip {Prov : Type}
    [DecidableEq Prov] [PointerProvenance Prov]
    (offset ptrSize : Size) (prov : Prov)
    (h_pne : ptrSize.bytes ≠ 0)
    (h_lt : offset.bytes.toNat + ptrSize.bytes.toNat < Nat.pow 2 64) :
    ∃ pm : ProvenanceMap Prov,
      ProvenanceMap.insertPtr offset prov ptrSize ProvenanceMap.new =
        .ok () pm ∧
      pm.getPtr offset = some prov ∧
      pm.readPtr offset ptrSize = .ok (some prov) := by
  have h_emp := provenanceMap_new_rangeEmpty (Prov := Prov)
    (allocRange offset ptrSize) ptrSize h_pne h_lt
  cases h_ins :
      ProvenanceMap.insertPtr offset prov ptrSize
        (ProvenanceMap.new (Prov := Prov)) with
  | error e s =>
    dsimp only [ProvenanceMap.insertPtr, bind, Bind.bind, EStateM.bind, pure,
      Pure.pure, EStateM.pure, EStateM.get, EStateM.set] at h_ins
    change
      (EStateM.bind (provCheckedMirror
          ((ProvenanceMap.new (Prov := Prov)).rangeEmpty
            (allocRange offset ptrSize) ptrSize))
        fun b => _) (ProvenanceMap.new (Prov := Prov)) =
      EStateM.Result.error e s at h_ins
    dsimp only [provCheckedMirror, EStateM.bind] at h_ins
    rw [h_emp] at h_ins
    dsimp only at h_ins
    rw [show (!true) = false from rfl, ite_false_eq] at h_ins
    cases h_ins
  | ok u pm =>
    have h_ins_eq := h_ins
    dsimp only [ProvenanceMap.insertPtr, bind, Bind.bind, EStateM.bind, pure,
      Pure.pure, EStateM.pure, EStateM.get, EStateM.set] at h_ins_eq
    change
      (EStateM.bind (provCheckedMirror
          ((ProvenanceMap.new (Prov := Prov)).rangeEmpty
            (allocRange offset ptrSize) ptrSize))
        fun b => _) (ProvenanceMap.new (Prov := Prov)) =
      EStateM.Result.ok u pm at h_ins_eq
    dsimp only [provCheckedMirror, EStateM.bind] at h_ins_eq
    rw [h_emp] at h_ins_eq
    dsimp only at h_ins_eq
    rw [show (!true) = false from rfl, ite_false_eq] at h_ins_eq
    injection h_ins_eq with _ h_pm_mk
    refine ⟨pm, rfl, ?_, ?_⟩
    · have h_get : pm.getPtr offset = some prov := by
        subst h_pm_mk
        have h_qs := Miri.Memory.QSortProof.singleton (offset, prov)
          (fun l r => l.1.bytes < r.1.bytes)
        change ((((Array.mk [(offset, prov)]).qsort
          (fun l r => l.1.bytes < r.1.bytes) 0 0).find?
          (fun e => e.1.bytes == offset.bytes)).map Prod.snd) = some prov
        rw [h_qs, ← Array.find?_toList]
        dsimp only [List.find?]
        rw [beq_self_eq_true]
        rfl
      exact h_get
    · apply ProvenanceMap.read_exact_pointer
      subst h_pm_mk
      have h_qs := Miri.Memory.QSortProof.singleton (offset, prov)
        (fun l r => l.1.bytes < r.1.bytes)
      change ((((Array.mk [(offset, prov)]).qsort
        (fun l r => l.1.bytes < r.1.bytes) 0 0).find?
        (fun e => e.1.bytes == offset.bytes)).map Prod.snd) = some prov
      rw [h_qs, ← Array.find?_toList]
      dsimp only [List.find?]
      rw [beq_self_eq_true]
      rfl

/-- Local mirror of `Miri.Memory.Allocation`'s private `checkedAlign`. -/
private def allocCheckedAlignMirror (align : Align) : Except AllocError Align :=
  Except.bind (Except.mapError AllocError.alignment (Align.bytes align))
    fun bytes =>
  Except.bind (Except.mapError AllocError.alignment (Align.fromBytes bytes))
    fun norm =>
  if (norm == align) = true then Except.ok align
  else Except.error (AllocError.alignment (AlignError.tooLarge bytes))

private theorem allocCheckedAlignMirror_ok (align : Align)
    (h : align.pow2 ≤ 29) :
    allocCheckedAlignMirror align = .ok align := by
  have h_ab := align_bytes_and_fromBytes_of_le_29 align.pow2 h
  dsimp only [allocCheckedAlignMirror]
  have h_ab1 :
      Align.bytes align = .ok (UInt64.ofNat (Nat.pow 2 align.pow2)) := h_ab.1
  rw [h_ab1]
  dsimp only [Except.mapError, Except.bind]
  rw [h_ab.2]
  dsimp only [Except.mapError, Except.bind]
  have h_beq : (({ pow2 := align.pow2 } : Align) == align) = true := by
    cases align
    exact beq_self_eq_true _
  rw [h_beq, ite_true_eq]

/-- Local mirror of `Miri.Memory.Allocation`'s private `sizeForArray`. -/
private def allocSizeForArrayMirror (length : Nat) : Except AllocError Size :=
  if 18446744073709551615 < length then
    Except.error (AllocError.storageLengthOverflow length)
  else
    let size := Size.ofBytes (UInt64.ofNat length)
    if (size.bytes.toNat == length) = true then Except.ok size
    else Except.error (AllocError.storageLengthOverflow length)

private theorem allocSizeForArrayMirror_ok {n : Nat} (hn : n < Nat.pow 2 64) :
    allocSizeForArrayMirror n = .ok (Size.ofBytes (UInt64.ofNat n)) := by
  dsimp only [allocSizeForArrayMirror]
  have h_nmax : ¬ (18446744073709551615 < n) :=
    Nat.not_lt.mpr (Nat.le_pred_of_lt hn)
  rw [ite_neg_eq h_nmax]
  have h_eq : ((Size.ofBytes (UInt64.ofNat n)).bytes.toNat == n) = true := by
    dsimp only [Size.ofBytes]
    rw [u64_ofNat_toNat_of_lt hn]
    exact beq_self_eq_true _
  rw [h_eq, ite_true_eq]

private theorem checkedSliceMirror_of_inbounds (bytes : Array UInt8)
    (start len : Nat) (h_sz : bytes.size < Nat.pow 2 64)
    (h_in : start + len ≤ bytes.size) :
    checkedSliceMirror bytes (Size.ofBytes (UInt64.ofNat bytes.size))
      (allocRange (Size.ofBytes (UInt64.ofNat start))
        (Size.ofBytes (UInt64.ofNat len))) =
      .ok (bytes.extract start (start + len)) := by
  have h_eq_sz :
      bytes.size = (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat :=
    (u64_ofNat_toNat_of_lt h_sz).symm
  have h_start_lt : start < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right start len) h_in) h_sz
  have h_len_lt : len < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left len start) h_in) h_sz
  have h_sum_lt : start + len < Nat.pow 2 64 := Nat.lt_of_le_of_lt h_in h_sz
  have h_s_toNat : (Size.ofBytes (UInt64.ofNat start)).bytes.toNat = start :=
    u64_ofNat_toNat_of_lt h_start_lt
  have h_l_toNat : (Size.ofBytes (UInt64.ofNat len)).bytes.toNat = len :=
    u64_ofNat_toNat_of_lt h_len_lt
  have h_end :
      (allocRange (Size.ofBytes (UInt64.ofNat start))
        (Size.ofBytes (UInt64.ofNat len))).endExclusive =
        .ok (Size.ofBytes (UInt64.ofNat (start + len))) := by
    have h_e := allocRange_endExclusive_of_lt
      (allocRange (Size.ofBytes (UInt64.ofNat start))
        (Size.ofBytes (UInt64.ofNat len)))
      (by dsimp only [allocRange]; rw [h_s_toNat, h_l_toNat]; exact h_sum_lt)
    dsimp only [allocRange] at h_e
    rw [h_s_toNat, h_l_toNat] at h_e
    exact h_e
  dsimp only [checkedSliceMirror]
  have h_nbne :
      (bytes.size !=
        (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat) = false := by
    rw [← h_eq_sz]
    exact bne_self_eq_false _
  rw [h_nbne, ite_false_eq]
  dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_end]
  dsimp only [Except.mapError, allocRange]
  have h_o1 : ¬ (UInt64.ofNat (start + len) < UInt64.ofNat start) :=
    u64_not_lt_of_le (by
      rw [u64_ofNat_toNat_of_lt h_sum_lt, u64_ofNat_toNat_of_lt h_start_lt]
      exact Nat.le_add_right _ _)
  have h_o2 : ¬ (UInt64.ofNat bytes.size < UInt64.ofNat (start + len)) :=
    u64_not_lt_of_le (by
      rw [u64_ofNat_toNat_of_lt h_sz, u64_ofNat_toNat_of_lt h_sum_lt]
      exact h_in)
  have h_ob :
      (decide (UInt64.ofNat (start + len) < UInt64.ofNat start) ||
        decide (UInt64.ofNat bytes.size < UInt64.ofNat (start + len))) =
        false := by
    rw [decide_eq_false h_o1, decide_eq_false h_o2]
    rfl
  change
    (if (decide (UInt64.ofNat (start + len) < UInt64.ofNat start) ||
        decide (UInt64.ofNat bytes.size < UInt64.ofNat (start + len))) = true
     then _ else _) = _
  rw [h_ob, ite_false_eq, h_s_toNat]
  dsimp only [Size.ofBytes]
  rw [u64_ofNat_toNat_of_lt h_sum_lt]

/-- Upstream `Miri.Memory.Allocation.fromBytes` succeeds for any byte array
with `bytes.size < 2^64` and `align.pow2 ≤ 29`, yielding exact size, alignment,
mutability, lazy initialized mask, empty provenance map, and exact
`getBytesUnchecked` / `getBytesStripProvenance` subslice reads. -/
theorem miriAlloc_fromBytes_spec {Prov Extra : Type} [PointerProvenance Prov]
    (bytes : Array UInt8) (align : Align)
    (mutability : Miri.Memory.Mutability) (extra : Extra)
    (h_sz : bytes.size < Nat.pow 2 64)
    (h_al : align.pow2 ≤ 29) :
    ∃ raw : Miri.Memory.Allocation Prov Unit,
      Miri.Memory.Allocation.fromBytes (Prov := Prov) bytes align mutability =
        .ok raw ∧
      let a := raw.withExtra extra
      a.len = bytes.size ∧
      a.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      a.align = align ∧
      a.mutability = mutability ∧
      a.provenanceMap = ProvenanceMap.new ∧
      a.initializationMask =
        InitMask.new (Size.ofBytes (UInt64.ofNat bytes.size)) true ∧
      (∀ (start len : Nat), start + len ≤ bytes.size →
        let r := allocRange (Size.ofBytes (UInt64.ofNat start))
          (Size.ofBytes (UInt64.ofNat len))
        a.getBytesUnchecked r = .ok (bytes.extract start (start + len)) ∧
        ∀ (layout : TargetDataLayout),
          a.getBytesStripProvenance layout r =
            .ok (bytes.extract start (start + len))) := by
  have h_eq_sz :
      bytes.size = (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat :=
    (u64_ofNat_toNat_of_lt h_sz).symm
  cases h_raw :
      Miri.Memory.Allocation.fromBytes (Prov := Prov) bytes align mutability
      with
  | error e =>
    dsimp only [Miri.Memory.Allocation.fromBytes, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure] at h_raw
    change
      (Except.bind (allocCheckedAlignMirror align) fun al =>
        Except.bind (allocSizeForArrayMirror bytes.size) fun sz => _) =
      Except.error e at h_raw
    rw [allocCheckedAlignMirror_ok align h_al] at h_raw
    dsimp only [Except.bind] at h_raw
    rw [allocSizeForArrayMirror_ok h_sz] at h_raw
    dsimp only [Except.bind] at h_raw
    rw [dite_pos_eq h_eq_sz] at h_raw
    cases h_raw
  | ok raw =>
    have h_raw_eq := h_raw
    dsimp only [Miri.Memory.Allocation.fromBytes, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure] at h_raw_eq
    change
      (Except.bind (allocCheckedAlignMirror align) fun al =>
        Except.bind (allocSizeForArrayMirror bytes.size) fun sz => _) =
      Except.ok raw at h_raw_eq
    rw [allocCheckedAlignMirror_ok align h_al] at h_raw_eq
    dsimp only [Except.bind] at h_raw_eq
    rw [allocSizeForArrayMirror_ok h_sz] at h_raw_eq
    dsimp only [Except.bind] at h_raw_eq
    rw [dite_pos_eq h_eq_sz] at h_raw_eq
    injection h_raw_eq with h_raw_mk
    refine ⟨raw, rfl, ?_⟩
    subst h_raw_mk
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro start len h_in
    have h_start_lt : start < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right start len) h_in) h_sz
    have h_len_lt : len < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left len start) h_in) h_sz
    have h_sum_lt : start + len < Nat.pow 2 64 := Nat.lt_of_le_of_lt h_in h_sz
    have h_s_toNat : (Size.ofBytes (UInt64.ofNat start)).bytes.toNat = start :=
      u64_ofNat_toNat_of_lt h_start_lt
    have h_l_toNat : (Size.ofBytes (UInt64.ofNat len)).bytes.toNat = len :=
      u64_ofNat_toNat_of_lt h_len_lt
    have h_slice := checkedSliceMirror_of_inbounds bytes start len h_sz h_in
    refine ⟨h_slice, ?_⟩
    intro layout
    dsimp only [Miri.Memory.Allocation.getBytesStripProvenance,
      Miri.Memory.Allocation.withExtra, bind, Bind.bind, Except.bind, pure,
      Pure.pure, Except.pure]
    let rng := allocRange (Size.ofBytes (UInt64.ofNat start))
      (Size.ofBytes (UInt64.ofNat len))
    have h_im := initMask_lazy_true_isRangeInitialized
      (Size.ofBytes (UInt64.ofNat bytes.size)) rng
      (by
        dsimp only [rng, allocRange]
        rw [h_s_toNat, h_l_toNat]
        exact h_sum_lt)
      (by
        dsimp only [rng, allocRange]
        rw [h_s_toNat, h_l_toNat, ← h_eq_sz]
        exact h_in)
    rw [h_im]
    dsimp only [Except.mapError]
    cases PointerProvenance.offsetIsAddr (Prov := Prov) with
    | true => rw [show (!true) = false from rfl, ite_false_eq]; exact h_slice
    | false =>
      rw [show (!false) = true from rfl, ite_true_eq]
      have h_pne : (Size.fromBits layout.pointerWidth.bits).bytes ≠ 0 := by
        cases layout.pointerWidth <;> decide
      have h_re := provenanceMap_new_rangeEmpty (Prov := Prov) rng
        (Size.fromBits layout.pointerWidth.bits) h_pne
        (by
          dsimp only [rng, allocRange]
          rw [h_s_toNat, h_l_toNat]
          exact h_sum_lt)
      change
        (Except.bind (Except.mapError AllocError.provenance
          ((ProvenanceMap.new (Prov := Prov)).rangeEmpty rng
            (Size.fromBits layout.pointerWidth.bits))) fun v => _) = _
      rw [h_re]
      dsimp only [Except.mapError, Except.bind]
      rw [show (!true) = false from rfl, ite_false_eq]
      exact h_slice

/-- Upstream `Miri.Memory.Allocation.writeBytes` on a mutable, initialized,
provenance-free `fromBytes` allocation succeeds for any in-bounds `patch`,
preserves `InitMask.new _ true` and `ProvenanceMap.new`, and updates the raw
bytes to the exact spliced array. -/
theorem miriAlloc_writeBytes_step {Prov Extra : Type} [PointerProvenance Prov]
    (old patch : Array UInt8) (align : Align) (extra : Extra)
    (start : Nat) (ptrSize : Size)
    (h_sz : old.size < Nat.pow 2 64)
    (h_al : align.pow2 ≤ 29)
    (h_in : start + patch.size ≤ old.size)
    (h_pne : ptrSize.bytes ≠ 0)
    (raw0 : Miri.Memory.Allocation Prov Unit)
    (h_fb0 :
      Miri.Memory.Allocation.fromBytes (Prov := Prov) old align .Mut =
        .ok raw0) :
    let updated := old.extract 0 start ++ patch ++
      old.extract (start + patch.size) old.size
    ∃ (raw1 : Miri.Memory.Allocation Prov Unit),
      Miri.Memory.Allocation.fromBytes (Prov := Prov) updated align .Mut =
        .ok raw1 ∧
      Miri.Memory.Allocation.writeBytes (Size.ofBytes (UInt64.ofNat start))
        patch ptrSize (raw0.withExtra extra) =
        .ok () (raw1.withExtra extra) := by
  intro updated
  have h_upd_sz : updated.size = old.size :=
    array_splice_size old patch start h_in
  have h_upd_lt : updated.size < Nat.pow 2 64 := by
    rw [h_upd_sz]; exact h_sz
  let ⟨raw1, h_fb1, _⟩ := miriAlloc_fromBytes_spec
    (Prov := Prov) updated align .Mut extra h_upd_lt h_al
  refine ⟨raw1, h_fb1, ?_⟩
  have h_eq0 : old.size = (Size.ofBytes (UInt64.ofNat old.size)).bytes.toNat :=
    (u64_ofNat_toNat_of_lt h_sz).symm
  dsimp only [Miri.Memory.Allocation.fromBytes, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure] at h_fb0
  change
    (Except.bind (allocCheckedAlignMirror align) fun al =>
      Except.bind (allocSizeForArrayMirror old.size) fun sz => _) =
    Except.ok raw0 at h_fb0
  rw [allocCheckedAlignMirror_ok align h_al] at h_fb0
  dsimp only [Except.bind] at h_fb0
  rw [allocSizeForArrayMirror_ok h_sz] at h_fb0
  dsimp only [Except.bind] at h_fb0
  rw [dite_pos_eq h_eq0] at h_fb0
  injection h_fb0 with h_mk0
  have h_eq1 :
      updated.size = (Size.ofBytes (UInt64.ofNat updated.size)).bytes.toNat :=
    (u64_ofNat_toNat_of_lt h_upd_lt).symm
  dsimp only [Miri.Memory.Allocation.fromBytes, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure] at h_fb1
  change
    (Except.bind (allocCheckedAlignMirror align) fun al =>
      Except.bind (allocSizeForArrayMirror updated.size) fun sz => _) =
    Except.ok raw1 at h_fb1
  rw [allocCheckedAlignMirror_ok align h_al] at h_fb1
  dsimp only [Except.bind] at h_fb1
  rw [allocSizeForArrayMirror_ok h_upd_lt] at h_fb1
  dsimp only [Except.bind] at h_fb1
  rw [dite_pos_eq h_eq1] at h_fb1
  injection h_fb1 with h_mk1
  subst h_mk0; subst h_mk1
  have h_p_lt : patch.size < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) h_in) h_sz
  have h_s_lt : start < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) h_in) h_sz
  have h_sum_lt : start + patch.size < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt h_in h_sz
  have h_s_toNat : (Size.ofBytes (UInt64.ofNat start)).bytes.toNat = start :=
    u64_ofNat_toNat_of_lt h_s_lt
  have h_p_toNat :
      (Size.ofBytes (UInt64.ofNat patch.size)).bytes.toNat = patch.size :=
    u64_ofNat_toNat_of_lt h_p_lt
  let rng := allocRange (Size.ofBytes (UInt64.ofNat start))
    (Size.ofBytes (UInt64.ofNat patch.size))
  have h_end :
      rng.endExclusive = .ok (Size.ofBytes (UInt64.ofNat (start + patch.size)))
      := by
    have h_e := allocRange_endExclusive_of_lt rng
      (by
        dsimp only [rng, allocRange]
        rw [h_s_toNat, h_p_toNat]
        exact h_sum_lt)
    dsimp only [rng, allocRange] at h_e
    rw [h_s_toNat, h_p_toNat] at h_e
    exact h_e
  have h_cs_ok := checkedSliceMirror_of_inbounds old start patch.size h_sz h_in
  dsimp only [Miri.Memory.Allocation.writeBytes,
    Miri.Memory.Allocation.withExtra, Id.run, bind, Bind.bind, pure, Pure.pure]
  change
    (match allocSizeForArrayMirror patch.size with
     | Except.ok size => _
     | Except.error reason => EStateM.Result.error reason _) = _
  rw [allocSizeForArrayMirror_ok h_p_lt]
  dsimp only
  change
    (match checkedSliceMirror old (Size.ofBytes (UInt64.ofNat old.size)) rng
     with
     | Except.error reason => EStateM.Result.error reason _
     | Except.ok _ => _) = _
  rw [h_cs_ok]
  dsimp only
  cases h_p0 : ((Size.ofBytes (UInt64.ofNat patch.size)).bytes == 0) with
  | true =>
    have h_pn0 : patch.size = 0 := by
      have h_u : UInt64.ofNat patch.size = 0 := eq_of_beq h_p0
      rw [← u64_ofNat_toNat_of_lt h_p_lt, h_u]
      rfl
    have h_upd_eq_old : updated = old := by
      apply Array.toList_inj.mp
      rw [array_splice_toList old patch start h_in]
      have h_pl : patch.toList = [] :=
        List.eq_nil_of_length_eq_zero
          (by rw [Array.length_toList]; exact h_pn0)
      rw [h_pl, h_pn0, Nat.add_zero, List.append_nil, List.take_append_drop]
    rw [ite_true_eq, h_upd_sz, h_upd_eq_old]
  | false =>
    rw [ite_false_eq]
    rw [show (Miri.Memory.Mutability.Mut != Miri.Memory.Mutability.Mut) = false
      from rfl, ite_false_eq]
    have h_sr := initMask_lazy_true_setRange_true
      (Size.ofBytes (UInt64.ofNat old.size)) rng
      (by
        dsimp only [rng, allocRange]
        rw [h_s_toNat, h_p_toNat]
        exact h_sum_lt)
      (by
        dsimp only [rng, allocRange]
        rw [h_s_toNat, h_p_toNat, ← h_eq0]
        exact h_in)
    have h_cl := provenanceMap_new_clear (Prov := Prov) rng old ptrSize h_pne
      (by
        dsimp only [rng, allocRange]
        rw [h_s_toNat, h_p_toNat]
        exact h_sum_lt)
    change
      (match Except.bind (Except.mapError AllocError.memory
          ((InitMask.new (Size.ofBytes (UInt64.ofNat old.size)) true).setRange
            rng true))
          (fun (_ : InitMask) =>
            (_ : Except AllocError (Miri.Memory.Allocation Prov Extra))) with
       | Except.ok (_ : Miri.Memory.Allocation Prov Extra) => _
       | Except.error reason => EStateM.Result.error reason _) = _
    rw [h_sr]
    dsimp only [Except.mapError, Except.bind, pure, Pure.pure, Except.pure]
    rw [h_cl]
    dsimp only
    change
      (match Except.bind (Except.mapError AllocError.memory rng.endExclusive)
          (fun (_ : Size) =>
            (_ : Except AllocError (Miri.Memory.Allocation Prov Extra))) with
       | Except.ok updated => EStateM.Result.ok () updated
       | Except.error reason => EStateM.Result.error reason _) = _
    rw [h_end]
    dsimp only [Except.mapError, Except.bind, pure, Pure.pure, Except.pure,
      rng, allocRange]
    have h_sum_toNat :
        (Size.ofBytes (UInt64.ofNat (start + patch.size))).bytes.toNat =
          start + patch.size := u64_ofNat_toNat_of_lt h_sum_lt
    have h_nbne_old :
        (old.size != (Size.ofBytes (UInt64.ofNat old.size)).bytes.toNat) =
          false := by
      rw [← h_eq0]
      exact bne_self_eq_false _
    have h_upd_def :
        old.extract 0 start ++ patch ++
          old.extract (start + patch.size) old.size = updated := rfl
    simp only [h_s_toNat, h_sum_toNat, h_upd_def, h_upd_sz, h_nbne_old,
      ite_false_eq]

/-- Upstream `Miri.Memory.Allocation.writeBytes` rejects any non-empty write
into an immutable (`.Not`) allocation with `.error .readOnlyAllocation`. -/
theorem miriAlloc_writeBytes_readonly_err {Prov Extra : Type}
    (old patch : Array UInt8) (align : Align) (extra : Extra)
    (start : Nat) (ptrSize : Size)
    (h_sz : old.size < Nat.pow 2 64)
    (h_al : align.pow2 ≤ 29)
    (h_in : start + patch.size ≤ old.size)
    (h_ne : 0 < patch.size)
    (raw0 : Miri.Memory.Allocation Prov Unit)
    (h_fb0 :
      Miri.Memory.Allocation.fromBytes (Prov := Prov) old align .Not =
        .ok raw0) :
    Miri.Memory.Allocation.writeBytes (Size.ofBytes (UInt64.ofNat start))
      patch ptrSize (raw0.withExtra extra) =
      .error .readOnlyAllocation (raw0.withExtra extra) := by
  have h_eq0 : old.size = (Size.ofBytes (UInt64.ofNat old.size)).bytes.toNat :=
    (u64_ofNat_toNat_of_lt h_sz).symm
  dsimp only [Miri.Memory.Allocation.fromBytes, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure] at h_fb0
  change
    (Except.bind (allocCheckedAlignMirror align) fun al =>
      Except.bind (allocSizeForArrayMirror old.size) fun sz => _) =
    Except.ok raw0 at h_fb0
  rw [allocCheckedAlignMirror_ok align h_al] at h_fb0
  dsimp only [Except.bind] at h_fb0
  rw [allocSizeForArrayMirror_ok h_sz] at h_fb0
  dsimp only [Except.bind] at h_fb0
  rw [dite_pos_eq h_eq0] at h_fb0
  injection h_fb0 with h_mk0; subst h_mk0
  have h_p_lt : patch.size < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) h_in) h_sz
  have h_cs_ok := checkedSliceMirror_of_inbounds old start patch.size h_sz h_in
  have h_pne0 :
      ((Size.ofBytes (UInt64.ofNat patch.size)).bytes == 0) = false := by
    cases h_eq : ((Size.ofBytes (UInt64.ofNat patch.size)).bytes == 0) with
    | false => rfl
    | true =>
      have h_u : UInt64.ofNat patch.size = 0 := eq_of_beq h_eq
      have h_z : patch.size = 0 := by
        rw [← u64_ofNat_toNat_of_lt h_p_lt, h_u]
        rfl
      exact False.elim (Nat.ne_of_gt h_ne h_z)
  let rng := allocRange (Size.ofBytes (UInt64.ofNat start))
    (Size.ofBytes (UInt64.ofNat patch.size))
  dsimp only [Miri.Memory.Allocation.writeBytes,
    Miri.Memory.Allocation.withExtra, Id.run, bind, Bind.bind, pure, Pure.pure]
  change
    (match allocSizeForArrayMirror patch.size with
     | Except.ok size => _
     | Except.error reason => EStateM.Result.error reason _) = _
  rw [allocSizeForArrayMirror_ok h_p_lt]
  dsimp only
  change
    (match checkedSliceMirror old (Size.ofBytes (UInt64.ofNat old.size)) rng
     with
     | Except.error reason => EStateM.Result.error reason _
     | Except.ok _ => _) = _
  rw [h_cs_ok]
  dsimp only
  rw [h_pne0, ite_false_eq]
  rfl

/-! ## Section 5: Tracked Slice & `CallerMemory` Simulation -/

/-- Translate `Trusted.MirAst.Mutability` to `Miri.Memory.Mutability`. -/
def toMiriMutability : MirAst.Mutability → Miri.Memory.Mutability
  | .shared => .Not
  | .mut => .Mut

/-- Simulation invariant relating a live, initialized, provenance-free
byte-slice `Trusted.MirSemantics.Allocation` (`&[u8]` or `&mut [u8]`) with raw
backing bytes `raw` to its `Miri.Memory.Allocation` image constructed via
`Allocation.fromBytes`. -/
def AllocByteSliceRel
    (raw : List UInt8)
    (a : MirSemantics.Allocation)
    (ma : Miri.Memory.Allocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree) : Prop :=
  a.live = true ∧
  a.alignLog2 ≤ 29 ∧
  a.bytes.length < Nat.pow 2 64 ∧
  a.bytes = raw.map (fun b => AllocByte.init b none) ∧
  ∃ (rawAlloc : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (extra : Miri.TreeBorrows.BorrowTree),
    Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
      (Array.mk raw) ⟨a.alignLog2⟩ (toMiriMutability a.mutability) =
        .ok rawAlloc ∧
    ma = rawAlloc.withExtra extra

/-- Construct `AllocByteSliceRel` for any live, initialized, provenance-free
byte-slice allocation with `alignLog2 ≤ 29` and `raw.length < 2^64`. -/
theorem allocByteSliceRel_of_initBytes (allocId alignLog2 : Nat)
    (mutability : MirAst.Mutability) (raw : List UInt8)
    (extra : Miri.TreeBorrows.BorrowTree)
    (h_al : alignLog2 ≤ 29) (h_lt : raw.length < Nat.pow 2 64) :
    let a : MirSemantics.Allocation := {
      allocId := allocId
      alignLog2 := alignLog2
      mutability := mutability
      bytes := raw.map (fun b => AllocByte.init b none)
      live := true
    }
    ∃ ma, AllocByteSliceRel raw a ma := by
  intro a
  let ⟨rawAlloc, h_fb, _⟩ := miriAlloc_fromBytes_spec
    (Prov := Miri.Memory.Provenance) (Array.mk raw) ⟨alignLog2⟩
    (toMiriMutability mutability) extra h_lt h_al
  refine ⟨rawAlloc.withExtra extra, rfl, h_al,
    by rw [List.length_map]; exact h_lt, rfl, rawAlloc, extra, h_fb, rfl⟩

/-- Read agreement under `AllocByteSliceRel`: for every in-bounds, properly
aligned subslice `(off, len)`, `Trusted.MirSemantics.readBytes` and
`Miri.Memory.Allocation.{getBytesUnchecked, getBytesStripProvenance}` agree
byte-for-byte. -/
theorem allocByteSliceRel_readBytes_agree
    {raw : List UInt8}
    {m : MirSemantics.MemoryState} {a : MirSemantics.Allocation}
    {ma : Miri.Memory.Allocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree}
    (h_rel : AllocByteSliceRel raw a ma)
    (h_fa : findAllocation a.allocId m.allocations = some a)
    (off len alignLog2 : Nat)
    (h_in : off + len ≤ raw.length)
    (h_al : MirSemantics.isAligned a off alignLog2 = true)
    (layout : TargetDataLayout) :
    let sub := (raw.drop off).take len
    readBytes m ⟨a.allocId, off⟩ len alignLog2 =
      .ok (sub.map (fun b => AllocByte.init b none)) ∧
    ma.getBytesUnchecked
        (allocRange (Size.ofBytes (UInt64.ofNat off))
          (Size.ofBytes (UInt64.ofNat len))) =
      .ok (Array.mk sub) ∧
    ma.getBytesStripProvenance layout
        (allocRange (Size.ofBytes (UInt64.ofNat off))
          (Size.ofBytes (UInt64.ofNat len))) =
      .ok (Array.mk sub) := by
  intro sub
  let ⟨h_live, h_align_le, h_size_lt, h_bytes_eq, rawAlloc, extra, h_fb_ok,
    h_miri_eq⟩ := h_rel
  have h_raw_lt : raw.length < Nat.pow 2 64 := by
    have h_s := h_size_lt
    rw [h_bytes_eq, List.length_map] at h_s
    exact h_s
  let ⟨rawAlloc', h_fb', _, _, _, _, _, _, h_reads⟩ :=
    miriAlloc_fromBytes_spec (Prov := Miri.Memory.Provenance)
      (Array.mk raw) ⟨a.alignLog2⟩ (toMiriMutability a.mutability)
      extra h_raw_lt h_align_le
  have h_ra_eq : rawAlloc = rawAlloc' := by
    have h1 := h_fb_ok
    rw [h_fb'] at h1
    injection h1 with h_eq
    exact h_eq.symm
  have h_sub_eq : (Array.mk raw).extract off (off + len) = Array.mk sub := by
    apply Array.toList_inj.mp
    rw [array_extract_toList, Nat.add_sub_cancel_left]
  let ⟨h_gb, h_gsp⟩ := h_reads off len h_in
  rw [h_sub_eq] at h_gb
  rw [h_sub_eq] at h_gsp
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [readBytes]
    rw [h_fa]
    dsimp only
    cases h_l0 : Nat.beq len 0 with
    | true =>
      have h_z : len = 0 := (nat_beq_true_iff _ _).1 h_l0
      subst h_z
      rw [h_al]
      rfl
    | false =>
      rw [ite_false_eq]
      rw [h_live]
      have h_ib : isInBounds a off len = true := by
        dsimp only [isInBounds]
        rw [h_bytes_eq, List.length_map]
        exact (nat_ble_true_iff _ _).2 h_in
      rw [h_ib, h_al]
      dsimp only [sub]
      rw [show (!true || !true || !true) = false from rfl, ite_false_eq,
        h_bytes_eq, ← List.map_drop, ← List.map_take]
  · rw [h_miri_eq, h_ra_eq]
    exact h_gb
  · rw [h_miri_eq, h_ra_eq]
    exact h_gsp layout

/-- Lockstep mutable byte-slice write under `AllocByteSliceRel`: mutating an
in-bounds, aligned slice `patch` in both `MirSemantics.writeBytes` and
`Miri.Memory.Allocation.writeBytes` succeeds, re-establishes
`AllocByteSliceRel` on the updated allocation pair, and preserves every
disjoint allocation in `MirSemantics.MemoryState`. -/
theorem allocByteSliceRel_writeBytes_step
    {raw : List UInt8}
    {m : MirSemantics.MemoryState} {a : MirSemantics.Allocation}
    {ma : Miri.Memory.Allocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree}
    (h_rel : AllocByteSliceRel raw a ma)
    (h_fa : findAllocation a.allocId m.allocations = some a)
    (h_mut : a.mutability = .mut)
    (off alignLog2 : Nat) (patch : List UInt8)
    (h_in : off + patch.length ≤ raw.length)
    (h_al : MirSemantics.isAligned a off alignLog2 = true) :
    let patchBytes := patch.map (fun b => AllocByte.init b none)
    let raw' := raw.take off ++ patch ++ raw.drop (off + patch.length)
    let a' : MirSemantics.Allocation :=
      { a with bytes := raw'.map (fun b => AllocByte.init b none) }
    ∃ (m' : MirSemantics.MemoryState)
      (ma' : Miri.Memory.Allocation Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree),
      writeBytes m ⟨a.allocId, off⟩ alignLog2 patchBytes = .ok m' ∧
      m'.nextAllocId = m.nextAllocId ∧
      findAllocation a.allocId m'.allocations = some a' ∧
      Miri.Memory.Allocation.writeBytes
        (Size.ofBytes (UInt64.ofNat off)) (Array.mk patch) (Size.ofBytes 8)
        ma = .ok () ma' ∧
      AllocByteSliceRel raw' a' ma' ∧
      (∀ id2, id2 ≠ a.allocId →
        findAllocation id2 m'.allocations =
          findAllocation id2 m.allocations) := by
  intro patchBytes raw' a'
  let ⟨h_live, h_align_le, h_size_lt, h_bytes_eq, rawAlloc, extra, h_fb_ok,
    h_miri_eq⟩ := h_rel
  have h_raw_lt : raw.length < Nat.pow 2 64 := by
    have h_s := h_size_lt
    rw [h_bytes_eq, List.length_map] at h_s
    exact h_s
  have h_fb0_mut :
      Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk raw) ⟨a.alignLog2⟩ .Mut = .ok rawAlloc := by
    have h_f := h_fb_ok
    rw [h_mut] at h_f
    exact h_f
  let ⟨raw1, h_fb1, h_mw⟩ := miriAlloc_writeBytes_step
    (Prov := Miri.Memory.Provenance)
    (Array.mk raw) (Array.mk patch) ⟨a.alignLog2⟩ extra
    off (Size.ofBytes 8) h_raw_lt h_align_le h_in (by decide)
    rawAlloc h_fb0_mut
  have h_upd_eq :
      (Array.mk raw).extract 0 off ++ Array.mk patch ++
        (Array.mk raw).extract (off + patch.length) raw.length =
      Array.mk raw' := by
    apply Array.toList_inj.mp
    exact array_splice_toList (Array.mk raw) (Array.mk patch) off h_in
  dsimp only [Array.size] at h_fb1
  rw [h_upd_eq] at h_fb1
  have h_bytes_upd :
      a.bytes.take off ++ patchBytes ++ a.bytes.drop (off + patchBytes.length) =
      raw'.map (fun b => AllocByte.init b none) := by
    dsimp only [patchBytes, raw']
    rw [h_bytes_eq, List.length_map, ← List.map_take, ← List.map_drop,
      List.map_append, List.map_append]
  have h_raw'_len : raw'.length = raw.length :=
    list_write_length raw patch off h_in
  have h_rel' : AllocByteSliceRel raw' a' (raw1.withExtra extra) := by
    refine ⟨h_live, h_align_le, ?_, rfl, raw1, extra, ?_, rfl⟩
    · dsimp only [a']
      rw [List.length_map, h_raw'_len]
      exact h_raw_lt
    · dsimp only [a']
      rw [h_mut]
      exact h_fb1
  cases h_p0 : Nat.beq patch.length 0 with
  | true =>
    have h_pn : patch = [] :=
      List.eq_nil_of_length_eq_zero ((nat_beq_true_iff _ _).1 h_p0)
    have h_raw'_eq : raw' = raw := by
      dsimp only [raw']
      rw [h_pn, List.length_nil, Nat.add_zero, List.append_nil,
        List.take_append_drop]
    have h_a'_eq : a' = a := by
      cases a with
      | mk id al mt bs lv =>
        dsimp only [a']
        rw [h_raw'_eq]
        dsimp only at h_bytes_eq
        rw [h_bytes_eq]
    refine ⟨m, raw1.withExtra extra, ?_, rfl, ?_, ?_, h_rel', fun _ _ => rfl⟩
    · dsimp only [writeBytes, patchBytes]
      rw [h_fa]
      dsimp only
      rw [h_pn, h_al]
      rfl
    · rw [h_a'_eq]; exact h_fa
    · rw [h_miri_eq]; exact h_mw
  | false =>
    have h_w_ok :
        writeBytes m ⟨a.allocId, off⟩ alignLog2 patchBytes =
          .ok { m with allocations := replaceAllocation a' m.allocations } := by
      dsimp only [writeBytes]
      have h_pl : Nat.beq patchBytes.length 0 = false := by
        dsimp only [patchBytes]
        rw [List.length_map]
        exact h_p0
      rw [h_fa]
      dsimp only
      rw [h_pl, ite_false_eq, h_live]
      have h_ib : isInBounds a off patchBytes.length = true := by
        dsimp only [isInBounds, patchBytes]
        rw [h_bytes_eq, List.length_map, List.length_map]
        exact (nat_ble_true_iff _ _).2 h_in
      rw [h_ib, h_al]
      rw [show (!true || !true || !true) = false from rfl, ite_false_eq, h_mut]
      dsimp only [a']
      rw [h_bytes_upd, h_mut, h_live]
    refine ⟨{ m with allocations := replaceAllocation a' m.allocations },
      raw1.withExtra extra, h_w_ok, rfl, ?_, ?_, h_rel', ?_⟩
    · exact findAllocation_replaceAllocation_eq a' m.allocations a h_fa
    · rw [h_miri_eq]; exact h_mw
    · intro id2 h_ne
      exact findAllocation_replaceAllocation_ne a' id2 h_ne m.allocations

/-- Read-only write-fault agreement under `AllocByteSliceRel`: when
`a.mutability = .shared` and `patch ≠ []`, both `MirSemantics.writeBytes`
(`.error .undefined`) and `Miri.Memory.Allocation.writeBytes`
(`.error .readOnlyAllocation`) reject the write. -/
theorem allocByteSliceRel_writeBytes_readonly_fault
    {raw : List UInt8}
    {m : MirSemantics.MemoryState} {a : MirSemantics.Allocation}
    {ma : Miri.Memory.Allocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree}
    (h_rel : AllocByteSliceRel raw a ma)
    (h_fa : findAllocation a.allocId m.allocations = some a)
    (h_sh : a.mutability = .shared)
    (off alignLog2 : Nat) (patch : List UInt8)
    (h_ne : patch ≠ [])
    (h_in : off + patch.length ≤ raw.length) :
    writeBytes m ⟨a.allocId, off⟩ alignLog2
        (patch.map (fun b => AllocByte.init b none)) = .error .undefined ∧
    Miri.Memory.Allocation.writeBytes
        (Size.ofBytes (UInt64.ofNat off)) (Array.mk patch) (Size.ofBytes 8)
        ma = .error .readOnlyAllocation ma := by
  let ⟨_, h_align_le, h_size_lt, h_bytes_eq, rawAlloc, extra, h_fb_ok,
    h_miri_eq⟩ := h_rel
  have h_raw_lt : raw.length < Nat.pow 2 64 := by
    have h_s := h_size_lt
    rw [h_bytes_eq, List.length_map] at h_s
    exact h_s
  have h_fb0_not :
      Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk raw) ⟨a.alignLog2⟩ .Not = .ok rawAlloc := by
    have h_f := h_fb_ok
    rw [h_sh] at h_f
    exact h_f
  have h_pos : 0 < patch.length := by
    cases patch with
    | nil => exact False.elim (h_ne rfl)
    | cons _ _ => exact Nat.zero_lt_succ _
  refine ⟨?_, ?_⟩
  · apply writeBytes_shared_fault m ⟨a.allocId, off⟩ alignLog2 _ a _ h_fa h_sh
    intro h_nil
    cases patch with
    | nil => exact h_ne rfl
    | cons _ _ => cases h_nil
  · rw [h_miri_eq]
    exact miriAlloc_writeBytes_readonly_err (Array.mk raw) (Array.mk patch)
      ⟨a.alignLog2⟩ extra off (Size.ofBytes 8) h_raw_lt h_align_le
      h_in h_pos rawAlloc h_fb0_not

private theorem list_find?_filter_push_self {α : Type} (xs : List α) (x : α)
    (p q : α → Bool)
    (h_disj : ∀ y, p y = true → q y = false)
    (h_qx : q x = true) :
    ((xs.filter p) ++ [x]).find? q = some x := by
  induction xs with
  | nil =>
    dsimp only [List.filter, List.nil_append, List.find?]
    rw [h_qx]
  | cons hd tl ih =>
    dsimp only [List.filter]
    cases hp : p hd with
    | false => exact ih
    | true =>
      dsimp only [List.cons_append, List.find?]
      rw [h_disj hd hp]
      exact ih

private theorem list_find?_filter_push_other {α : Type} (xs : List α) (x : α)
    (p q : α → Bool)
    (h_keep : ∀ y, q y = true → p y = true)
    (h_qx : q x = false) :
    ((xs.filter p) ++ [x]).find? q = xs.find? q := by
  induction xs with
  | nil =>
    dsimp only [List.filter, List.nil_append, List.find?]
    rw [h_qx]
  | cons hd tl ih =>
    dsimp only [List.filter, List.find?]
    cases hq : q hd with
    | true =>
      rw [h_keep hd hq]
      dsimp only [List.cons_append, List.find?]
      rw [hq]
    | false =>
      cases hp : p hd with
      | false => exact ih
      | true =>
        dsimp only [List.cons_append, List.find?]
        rw [hq]
        exact ih

/-- Updating a live allocation in Miri's real `Miri.Memory.MemoryState` via
`setLiveAllocation` installs `{ entry with allocation := ma' }` at `mid` while
preserving `live.find?` on every distinct `mid2 ≠ mid`. -/
theorem miriMemoryState_setLiveAllocation_self_and_other
    {Prov Extra MachineKind : Type} [DecidableEq MachineKind]
    (st : Miri.Memory.MemoryState Prov Extra MachineKind)
    (mid : Miri.Memory.AllocId)
    (entry : Miri.Memory.LocalAllocation Prov Extra MachineKind)
    (ma' : Miri.Memory.Allocation Prov Extra)
    (h_find : st.live.find? (fun row => row.1 == mid) = some (mid, entry)) :
    ∃ st' : Miri.Memory.MemoryState Prov Extra MachineKind,
      st.setLiveAllocation mid ma' = .ok st' ∧
      st'.live.find? (fun row => row.1 == mid) =
        some (mid, { entry with allocation := ma' }) ∧
      (∀ mid2 : Miri.Memory.AllocId, mid2 ≠ mid →
        st'.live.find? (fun row => row.1 == mid2) =
          st.live.find? (fun row => row.1 == mid2)) := by
  have h_set := Miri.Memory.MemoryState.setLiveAllocation_of_find
    st mid entry ma' h_find
  refine ⟨_, h_set, ?_, ?_⟩
  · rw [← Array.find?_toList, Array.toList_push, Array.toList_filter]
    apply list_find?_filter_push_self
    · intro y hy
      cases h_eq : (y.1 == mid) with
      | false => rfl
      | true =>
        dsimp only [bne] at hy
        rw [h_eq] at hy
        cases hy
    · exact beq_self_eq_true mid
  · intro mid2 h_ne
    rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_push,
      Array.toList_filter]
    apply list_find?_filter_push_other
    · intro y hy
      have h_ym : y.1 = mid2 := eq_of_beq hy
      rw [h_ym]
      cases h_eq : (mid2 == mid) with
      | false =>
        dsimp only [bne]
        rw [h_eq]
        rfl
      | true => exact False.elim (h_ne (eq_of_beq h_eq))
    · cases h_eq : (mid == mid2) with
      | false => rfl
      | true => exact False.elim (h_ne (eq_of_beq h_eq).symm)

/-- Whenever `(mid, entry)` is present in `st.live`, `st.getAllocInfo mid`
returns `.liveData` with `entry.allocation`'s size, alignment, and mutability.
-/
theorem miriMemoryState_getAllocInfo_live {Prov Extra MachineKind : Type}
    (st : Miri.Memory.MemoryState Prov Extra MachineKind)
    (mid : Miri.Memory.AllocId)
    (entry : Miri.Memory.LocalAllocation Prov Extra MachineKind)
    (h_find : st.live.find? (fun row => row.1 == mid) = some (mid, entry)) :
    st.getAllocInfo mid =
      .ok ⟨entry.allocation.byteSize, entry.allocation.align, .liveData,
        entry.allocation.mutability⟩ := by
  unfold Miri.Memory.MemoryState.getAllocInfo
  rw [h_find]
  rfl

/-- Tracked byte-slice correspondence between `MirSemantics.MemoryState` and
Miri's real `Miri.Memory.MemoryState`, scoped to an explicit list of allocation
IDs `tracked : List MirAst.AllocId` so uninitialized stack allocations
(`allocateStack`) and deallocated stack slots (`deallocateStack`) outside
`tracked` coexist cleanly in `m`. -/
def TrackedSliceMemRel
    (tracked : List MirAst.AllocId)
    (m : MirSemantics.MemoryState)
    (miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit) : Prop :=
  ∀ id : MirAst.AllocId, id ∈ tracked →
    0 < id ∧ id < m.nextAllocId ∧ id < Nat.pow 2 64 ∧
    ∃ (a : MirSemantics.Allocation) (raw : List UInt8)
      (mid : Miri.Memory.AllocId)
      (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit),
      mid.value = UInt64.ofNat id ∧
      findAllocation id m.allocations = some a ∧
      miriMem.live.find? (fun row => row.1 == mid) = some (mid, entry) ∧
      AllocByteSliceRel raw a entry.allocation

/-- Snapshot bridge between `Trusted.MirSemantics.CallerMemory`
(`State.callerMem`) and `TrackedSliceMemRel`: every tracked ID in `cm` agrees
with `findAllocation` in `m` and is related to `miriMem` via
`TrackedSliceMemRel`. Note that `MirSemantics.initState` currently rejects
non-empty `callerMem` (`State.lean`) and `evalStep` threads `callerMem` through
unchanged, so non-empty `tracked` instantiations of `CallerMemorySliceRel` are
forward-looking until pointer and reference entry arguments land
(`Boundary.lean`). -/
def CallerMemorySliceRel
    (cm : CallerMemory)
    (tracked : List MirAst.AllocId)
    (m : MirSemantics.MemoryState)
    (miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit) : Prop :=
  TrackedSliceMemRel tracked m miriMem ∧
  ∀ id : MirAst.AllocId, id ∈ tracked →
    findAllocation id cm.allocations = findAllocation id m.allocations

/-- `allocateStack` creates an `.uninit` stack slot at a fresh ID outside
`tracked` while preserving `TrackedSliceMemRel` and `MemoryAllIdsLt`. -/
theorem trackedSliceMemRel_allocateStack
    {tracked : List MirAst.AllocId}
    {m : MirSemantics.MemoryState}
    {miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    (layout : MirSemantics.LayoutData)
    (h_fresh : MemoryAllIdsLt m)
    (h_rel : TrackedSliceMemRel tracked m miriMem) :
    let res := allocateStack m layout
    ¬ (res.2.allocId ∈ tracked) ∧
    MemoryAllIdsLt res.1 ∧
    TrackedSliceMemRel tracked res.1 miriMem := by
  let ⟨h_pl, h_next, h_fr', _, h_keep⟩ := allocateStack_spec m layout h_fresh
  refine ⟨?_, h_fr', ?_⟩
  · intro h_in
    have h_lt := (h_rel (allocateStack m layout).2.allocId h_in).2.1
    rw [h_pl] at h_lt
    exact Nat.lt_irrefl m.nextAllocId h_lt
  · intro id h_in
    let ⟨h_pos, h_lt, h_lt64, a, raw, mid, entry, h_mid, h_fa, h_mf, h_ab⟩ :=
      h_rel id h_in
    refine ⟨h_pos, ?_, h_lt64, a, raw, mid, entry, h_mid,
      h_keep id a h_fa, h_mf, h_ab⟩
    rw [h_next]
    exact Nat.lt_succ_of_lt h_lt

/-- `writeBytes` to any untracked allocation `¬ (place.allocId ∈ tracked)` (such
as a stack local) preserves `TrackedSliceMemRel` with an unchanged `miriMem`. -/
theorem trackedSliceMemRel_writeBytes_untracked
    {tracked : List MirAst.AllocId}
    {m m' : MirSemantics.MemoryState}
    {miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    {place : MemPlace} {alignLog2 : Nat} {bs : List AllocByte}
    (h_fresh : MemoryAllIdsLt m)
    (h_rel : TrackedSliceMemRel tracked m miriMem)
    (h_untracked : ¬ (place.allocId ∈ tracked))
    (h_w : writeBytes m place alignLog2 bs = .ok m') :
    MemoryAllIdsLt m' ∧ TrackedSliceMemRel tracked m' miriMem := by
  let ⟨h_fr', h_next⟩ := memoryAllIdsLt_writeBytes h_fresh h_w
  refine ⟨h_fr', ?_⟩
  intro id h_in
  have h_ne : id ≠ place.allocId := fun h_eq => by
    rw [h_eq] at h_in
    exact h_untracked h_in
  let ⟨h_pos, h_lt, h_lt64, a, raw, mid, entry, h_mid, h_fa, h_mf, h_ab⟩ :=
    h_rel id h_in
  have h_fa' : findAllocation id m'.allocations = some a := by
    rw [(writeBytes_preserves_other_alloc m m' place alignLog2 bs
      h_w id h_ne).1]
    exact h_fa
  rw [h_next]
  exact ⟨h_pos, h_lt, h_lt64, a, raw, mid, entry, h_mid, h_fa', h_mf, h_ab⟩

/-- `storeIndirect` on an untracked stack slot `¬ (place.allocId ∈ tracked)`
preserves `TrackedSliceMemRel` and `MemoryAllIdsLt`. -/
theorem trackedSliceMemRel_storeIndirect_untracked
    {tracked : List MirAst.AllocId}
    {m m' : MirSemantics.MemoryState}
    {miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    {ty : MirTy} {place : MemPlace} {v : Val}
    (h_fresh : MemoryAllIdsLt m)
    (h_rel : TrackedSliceMemRel tracked m miriMem)
    (h_untracked : ¬ (place.allocId ∈ tracked))
    (h_st : storeIndirect m ty place v = .ok m') :
    MemoryAllIdsLt m' ∧ TrackedSliceMemRel tracked m' miriMem := by
  dsimp only [storeIndirect] at h_st
  cases h_lay : layoutOfTy ty with
  | none => rw [h_lay] at h_st; cases h_st
  | some lay =>
    rw [h_lay] at h_st
    cases h_enc : encodeVal profileTargetEndian ty v with
    | error _ => rw [h_enc] at h_st; cases h_st
    | ok bs =>
      rw [h_enc] at h_st
      exact trackedSliceMemRel_writeBytes_untracked
        h_fresh h_rel h_untracked h_st

/-- `deallocateStack` on an untracked stack slot `¬ (place.allocId ∈ tracked)`
marks the stack slot dead (`live = false`) while preserving `TrackedSliceMemRel`
and `MemoryAllIdsLt`. -/
theorem trackedSliceMemRel_deallocateStack_untracked
    {tracked : List MirAst.AllocId}
    {m m' : MirSemantics.MemoryState}
    {miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    {place : MemPlace}
    (h_fresh : MemoryAllIdsLt m)
    (h_rel : TrackedSliceMemRel tracked m miriMem)
    (h_untracked : ¬ (place.allocId ∈ tracked))
    (h_d : deallocateStack m place = .ok m') :
    MemoryAllIdsLt m' ∧ TrackedSliceMemRel tracked m' miriMem := by
  let ⟨h_fr', h_next⟩ := memoryAllIdsLt_deallocateStack h_fresh h_d
  let ⟨_, _, _, _, h_other⟩ := deallocateStack_spec m m' place h_d
  refine ⟨h_fr', ?_⟩
  intro id h_in
  have h_ne : id ≠ place.allocId := fun h_eq => by
    rw [h_eq] at h_in
    exact h_untracked h_in
  let ⟨h_pos, h_lt, h_lt64, a, raw, mid, entry, h_mid, h_fa, h_mf, h_ab⟩ :=
    h_rel id h_in
  rw [h_next]
  refine ⟨h_pos, h_lt, h_lt64, a, raw, mid, entry, h_mid, ?_, h_mf, h_ab⟩
  rw [h_other id h_ne]
  exact h_fa

/-- Lockstep mutable write on a tracked slice `targetId ∈ tracked`: mutating
`targetId` via `MirSemantics.writeBytes` and updating Miri's real
`Miri.Memory.MemoryState` via `setLiveAllocation` succeeds, updates `targetId`
to the concrete `a'` in `m'`, preserves `TrackedSliceMemRel` across all
`tracked` IDs, preserves `CallerMemorySliceRel` for the concrete `cm'` updating
`targetId` via `replaceAllocation`, and leaves every other allocation
(`id2 ≠ targetId` in `m'`, `mid2 ≠ mid` in `miriMem'.live`) untouched. -/
theorem trackedSliceMemRel_writeBytes_tracked_step
    {cm : CallerMemory}
    {tracked : List MirAst.AllocId}
    {m : MirSemantics.MemoryState}
    {miriMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    (h_cm : CallerMemorySliceRel cm tracked m miriMem)
    {targetId : MirAst.AllocId}
    (h_mem_tr : targetId ∈ tracked)
    {a : MirSemantics.Allocation}
    (h_fa : findAllocation targetId m.allocations = some a)
    (h_mut : a.mutability = .mut)
    (off alignLog2 : Nat) (patch : List UInt8)
    (h_al : MirSemantics.isAligned a off alignLog2 = true)
    (h_in : off + patch.length ≤ a.bytes.length) :
    let patchBytes := patch.map (fun b => AllocByte.init b none)
    let a' : MirSemantics.Allocation := {
      a with
      bytes :=
        a.bytes.take off ++ patchBytes ++
          a.bytes.drop (off + patchBytes.length)
    }
    let cm' : CallerMemory :=
      ⟨if Nat.beq patch.length 0 then cm.allocations
       else replaceAllocation a' cm.allocations⟩
    ∃ (m' : MirSemantics.MemoryState)
      (mid : Miri.Memory.AllocId)
      (kind : Miri.Memory.MemoryKind Unit)
      (ma ma' : Miri.Memory.Allocation Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree)
      (miriMem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit),
      mid.value = UInt64.ofNat targetId ∧
      miriMem.live.find? (fun row => row.1 == mid) =
        some (mid, ⟨kind, ma⟩) ∧
      miriMem'.live.find? (fun row => row.1 == mid) =
        some (mid, ⟨kind, ma'⟩) ∧
      writeBytes m ⟨targetId, off⟩ alignLog2 patchBytes = .ok m' ∧
      findAllocation targetId m'.allocations = some a' ∧
      Miri.Memory.Allocation.writeBytes
        (Size.ofBytes (UInt64.ofNat off)) (Array.mk patch) (Size.ofBytes 8)
        ma = .ok () ma' ∧
      miriMem.setLiveAllocation mid ma' = .ok miriMem' ∧
      CallerMemorySliceRel cm' tracked m' miriMem' ∧
      (∀ id2, id2 ≠ targetId →
        findAllocation id2 m'.allocations =
          findAllocation id2 m.allocations) ∧
      (∀ mid2 : Miri.Memory.AllocId, mid2 ≠ mid →
        miriMem'.live.find? (fun row => row.1 == mid2) =
          miriMem.live.find? (fun row => row.1 == mid2)) := by
  intro patchBytes a' cm'
  let ⟨h_tr, h_cm_eq⟩ := h_cm
  let ⟨_, _, _, a0, raw, mid, entry, h_mid, h_fa0, h_mf, h_rel⟩ :=
    h_tr targetId h_mem_tr
  have h_a_eq : a0 = a := by
    rw [h_fa] at h_fa0
    injection h_fa0 with h_eq
    exact h_eq.symm
  rw [h_a_eq] at h_rel
  have h_aid : a.allocId = targetId := (findAllocation_mem h_fa).2
  have h_fa_aid : findAllocation a.allocId m.allocations = some a := by
    rw [h_aid]
    exact h_fa
  have h_in_raw : off + patch.length ≤ raw.length := by
    rw [h_rel.2.2.2.1, List.length_map] at h_in
    exact h_in
  let raw' := raw.take off ++ patch ++ raw.drop (off + patch.length)
  let a_raw' : MirSemantics.Allocation :=
    { a with bytes := raw'.map (fun b => AllocByte.init b none) }
  have h_bytes_upd :
      a.bytes.take off ++ patchBytes ++
        a.bytes.drop (off + patchBytes.length) =
      raw'.map (fun b => AllocByte.init b none) := by
    dsimp only [patchBytes, raw']
    rw [h_rel.2.2.2.1, List.length_map, ← List.map_take, ← List.map_drop,
      List.map_append, List.map_append]
  have h_a'_eq : a' = a_raw' := by
    dsimp only [a', a_raw']
    rw [h_bytes_upd]
  let ⟨m', ma', h_w_raw, h_next, h_fa'_raw, h_mw, h_rel'_raw, h_other⟩ :=
    allocByteSliceRel_writeBytes_step h_rel h_fa_aid h_mut off alignLog2 patch
      h_in_raw h_al
  have h_w : writeBytes m ⟨targetId, off⟩ alignLog2 patchBytes = .ok m' := by
    rw [← h_aid]
    exact h_w_raw
  have h_fa' : findAllocation targetId m'.allocations = some a' := by
    rw [h_a'_eq, ← h_aid]
    exact h_fa'_raw
  have h_rel' : AllocByteSliceRel raw' a' ma' := by
    rw [h_a'_eq]
    exact h_rel'_raw
  let ⟨miriMem', h_set, h_mf_self, h_mf_other⟩ :=
    miriMemoryState_setLiveAllocation_self_and_other miriMem mid entry ma' h_mf
  have h_tr' : TrackedSliceMemRel tracked m' miriMem' := by
    intro id2 h2
    let ⟨hp2, hlt2, hlt64_2, a2, raw2, mid2, entry2, hm2, hfa2, hmf2, hr2⟩ :=
      h_tr id2 h2
    rw [h_next]
    cases h_eq : Nat.beq id2 targetId with
    | true =>
      have h_id_eq : id2 = targetId := (nat_beq_true_iff _ _).1 h_eq
      subst h_id_eq
      have h_mid_eq : mid2 = mid := by
        cases mid2 with
        | mk v2 nz2 =>
          cases mid with
          | mk v1 nz1 =>
            dsimp only at hm2 h_mid
            have hv : v2 = v1 := hm2.trans h_mid.symm
            subst hv
            rfl
      subst h_mid_eq
      exact ⟨hp2, hlt2, hlt64_2, a', raw', mid2,
        { entry with allocation := ma' }, h_mid, h_fa', h_mf_self, h_rel'⟩
    | false =>
      have h_ne : id2 ≠ targetId := fun h => by
        rw [(nat_beq_true_iff _ _).2 h] at h_eq
        cases h_eq
      have h_ne_aid : id2 ≠ a.allocId := by
        rw [h_aid]
        exact h_ne
      have h_mid_ne : mid2 ≠ mid := fun hm_eq => by
        have hv : mid2.value.toNat = mid.value.toNat :=
          congrArg (fun x : Miri.Memory.AllocId => x.value.toNat) hm_eq
        rw [hm2, h_mid, u64_ofNat_toNat_of_lt hlt64_2,
          u64_ofNat_toNat_of_lt (h_tr targetId h_mem_tr).2.2.1] at hv
        exact h_ne hv
      refine ⟨hp2, hlt2, hlt64_2, a2, raw2, mid2, entry2, hm2, ?_, ?_, hr2⟩
      · rw [h_other id2 h_ne_aid]
        exact hfa2
      · rw [h_mf_other mid2 h_mid_ne]
        exact hmf2
  have h_cm' : CallerMemorySliceRel cm' tracked m' miriMem' := by
    refine ⟨h_tr', ?_⟩
    intro id2 h2
    dsimp only [cm']
    cases h_p0 : Nat.beq patch.length 0 with
    | true =>
      rw [ite_true_eq]
      have h_pn : patch = [] :=
        List.eq_nil_of_length_eq_zero ((nat_beq_true_iff _ _).1 h_p0)
      have h_m'_eq : m' = m := by
        dsimp only [writeBytes, patchBytes] at h_w
        rw [h_fa] at h_w
        dsimp only at h_w
        rw [h_pn, h_al] at h_w
        dsimp only [List.map, List.length, Nat.beq, ite_true_eq] at h_w
        injection h_w with h_eq
        exact h_eq.symm
      rw [h_m'_eq]
      exact h_cm_eq id2 h2
    | false =>
      rw [ite_false_eq]
      have h_a'_id : a'.allocId = targetId := h_aid
      cases h_eq : Nat.beq id2 targetId with
      | true =>
        have h_id_eq : id2 = targetId := (nat_beq_true_iff _ _).1 h_eq
        subst h_id_eq
        have h_cm_fa : findAllocation id2 cm.allocations = some a := by
          rw [h_cm_eq id2 h2]
          exact h_fa
        rw [h_fa']
        exact Eq.trans
          (congrArg (fun k => findAllocation k
            (replaceAllocation a' cm.allocations)) h_a'_id.symm)
          (findAllocation_replaceAllocation_eq a' cm.allocations a
            (Eq.trans
              (congrArg (fun k => findAllocation k cm.allocations) h_a'_id)
              h_cm_fa))
      | false =>
        have h_ne : id2 ≠ targetId := fun h => by
          rw [(nat_beq_true_iff _ _).2 h] at h_eq
          cases h_eq
        have h_ne_a' : id2 ≠ a'.allocId := by
          rw [h_a'_id]
          exact h_ne
        have h_ne_a : id2 ≠ a.allocId := by
          rw [h_aid]
          exact h_ne
        rw [findAllocation_replaceAllocation_ne a' id2 h_ne_a' cm.allocations,
          h_other id2 h_ne_a]
        exact h_cm_eq id2 h2
  refine ⟨m', mid, entry.kind, entry.allocation, ma', miriMem', h_mid,
    ?_, ?_, h_w, h_fa', h_mw, h_set, h_cm', ?_, h_mf_other⟩
  · cases entry; exact h_mf
  · cases entry; exact h_mf_self
  · intro id2 h_ne
    apply h_other id2
    rw [h_aid]
    exact h_ne

/-! ## Section 6: 64-Bit Pointer Offsets, Bounds & Provenance Round-Trip -/

/-- Standard 64-bit target pointer arithmetic (`pointerSize = 8`). -/
def ptrArith64 : PointerArithmetic := ⟨Size.ofBytes 8⟩

/-- On 64-bit targets, `truncateToTargetUsize` is the identity on `UInt64`. -/
theorem ptrArith64_truncateToTargetUsize (v : UInt64) :
    ptrArith64.truncateToTargetUsize v = .ok v := by
  dsimp only [ptrArith64, PointerArithmetic.truncateToTargetUsize,
    Size.truncate, Size.bits, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure]
  let extBv :=
    BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 v.toNat))
  have h_ext : extBv.toNat = v.toNat := by
    dsimp only [extBv, BitVec.extractLsb, BitVec.extractLsb']
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h_vlt64 : v.toNat < Nat.pow 2 64 := u64_toNat_lt_pow64 v
    have h_vlt128 : v.toNat < Nat.pow 2 128 := Nat.lt_trans h_vlt64 (by decide)
    rw [Nat.mod_eq_of_lt h_vlt128, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt h_vlt64, Nat.mod_eq_of_lt h_vlt128]
  change
    (if extBv.toNat < Nat.pow 2 64 then Except.ok (UInt64.ofNat extBv.toNat)
     else Except.error PointerError.unsignedConversionOverflow) = Except.ok v
  rw [h_ext, ite_pos_eq (u64_toNat_lt_pow64 v)]
  apply congrArg Except.ok
  exact u64_eq_of_toNat_eq (u64_ofNat_toNat_of_lt (u64_toNat_lt_pow64 v))

/-- Exact 64-bit `targetUsizeMax` and `maxSizeOfVal`. -/
theorem ptrArith64_limits :
    ptrArith64.targetUsizeMax = .ok (UInt64.ofNat (Nat.pow 2 64 - 1)) ∧
    ptrArith64.maxSizeOfVal =
      .ok (Size.ofBytes (UInt64.ofNat (Nat.pow 2 63 - 1))) := by
  decide

/-- 64-bit `Pointer.wrappingOffset` computes exact wrapping 64-bit byte addition
while unconditionally preserving provenance. -/
theorem pointer_wrappingOffset_64 {Prov : Type}
    (ptr : Miri.Memory.Pointer Prov) (delta : Size) :
    ptr.wrappingOffset delta ptrArith64 =
      .ok { ptr with offset := Size.ofBytes (ptr.offset.bytes + delta.bytes) }
      := by
  dsimp only [Miri.Memory.Pointer.wrappingOffset, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure]
  rw [ptrArith64_truncateToTargetUsize]

/-- 64-bit `Pointer.wrappingSignedOffset` computes exact signed wrapping 64-bit
byte addition while unconditionally preserving provenance. -/
theorem pointer_wrappingSignedOffset_64 {Prov : Type}
    (ptr : Miri.Memory.Pointer Prov) (delta : Int64) :
    ptr.wrappingSignedOffset delta ptrArith64 =
      .ok {
        ptr with offset := Size.ofBytes (ptr.offset.bytes + delta.toUInt64)
      } :=
  pointer_wrappingOffset_64 ptr (Size.ofBytes delta.toUInt64)

private theorem negSucc_le_negSucc_iff (a b : Nat) :
    (Int.negSucc a ≤ Int.negSucc b) ↔ b ≤ a := by
  change Int.NonNeg (Int.subNatNat (a + 1) (b + 1)) ↔ b ≤ a
  dsimp only [Int.subNatNat]
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
  constructor
  · intro h_nn
    cases Nat.lt_or_ge a b with
    | inr h_le => exact h_le
    | inl h_gt =>
      have h_pos : 0 < b - a := Nat.sub_pos_of_lt h_gt
      cases h_sub : b - a with
      | zero => rw [h_sub] at h_pos; exact False.elim (Nat.lt_irrefl 0 h_pos)
      | succ k => rw [h_sub] at h_nn; cases h_nn
  · intro h_le
    rw [Nat.sub_eq_zero_of_le h_le]
    exact Int.NonNeg.mk (a - b)

private def fitsI64Mirror (value : Int) : Bool :=
  decide (Int.negSucc 9223372036854775807 ≤ value) &&
    decide (value < Int.ofNat 9223372036854775808)

private theorem fitsI64Mirror_ofNat {sz : Nat} (h_sz : sz < Nat.pow 2 63) :
    fitsI64Mirror (Int.ofNat sz) = true := by
  dsimp only [fitsI64Mirror]
  have h1 : Int.negSucc 9223372036854775807 ≤ Int.ofNat sz :=
    Int.le_trans (Int.negSucc_le_zero _) (Int.natCast_nonneg sz)
  have h2 : Int.ofNat sz < Int.ofNat 9223372036854775808 :=
    Int.ofNat_lt.2 h_sz
  rw [decide_eq_true h1, decide_eq_true h2]
  rfl

private theorem fitsI64Mirror_negSucc {k : Nat}
    (hk : k ≤ 9223372036854775807) :
    fitsI64Mirror (Int.negSucc k) = true := by
  dsimp only [fitsI64Mirror]
  have h1 : Int.negSucc 9223372036854775807 ≤ Int.negSucc k :=
    (negSucc_le_negSucc_iff _ _).2 hk
  have h2 : Int.negSucc k < Int.ofNat 9223372036854775808 :=
    Int.lt_of_lt_of_le (Int.negSucc_lt_zero k) (Int.natCast_nonneg _)
  rw [decide_eq_true h1, decide_eq_true h2]
  rfl

private theorem fitsI64Mirror_negSucc_outside {k : Nat}
    (hk : 9223372036854775807 < k) :
    fitsI64Mirror (Int.negSucc k) = false := by
  dsimp only [fitsI64Mirror]
  have h1 : ¬ (Int.negSucc 9223372036854775807 ≤ Int.negSucc k) :=
    fun h => Nat.not_lt.2 ((negSucc_le_negSucc_iff _ _).1 h) hk
  rw [decide_eq_false h1]
  rfl

private theorem ptrArith64_signExtendToTargetIsize_ok (v : UInt64) :
    ∃ signedOff : Int64,
      ptrArith64.signExtendToTargetIsize v = .ok signedOff := by
  dsimp only [ptrArith64, PointerArithmetic.signExtendToTargetIsize,
    Size.signExtend, Size.bits, bind, Bind.bind, Except.bind, pure, Pure.pure,
    Except.pure]
  let low := BitVec.extractLsb 63 0 (BitVec.ofNat 128 v.toNat)
  let bv := BitVec.signExtend 128 low
  have h_range :
      Int.negSucc 9223372036854775807 ≤ bv.toInt ∧
      bv.toInt < Int.ofNat 9223372036854775808 := by
    have h_eq : bv.toInt = low.toInt :=
      BitVec.toInt_signExtend_of_le (by decide)
    rw [h_eq]
    exact ⟨BitVec.le_toInt (x := low), BitVec.toInt_lt (x := low)⟩
  refine ⟨Int64.ofInt bv.toInt, ?_⟩
  change
    (if Int.negSucc 9223372036854775807 ≤ bv.toInt ∧
        bv.toInt < Int.ofNat 9223372036854775808 then
      Except.ok (Int64.ofInt bv.toInt)
     else Except.error PointerError.signedConversionOverflow) = _
  rw [ite_pos_eq h_range]

private def checkedBoundsMirror (target : PointerArithmetic)
    (id : Miri.Memory.AllocId) (allocSize offset : Size)
    (signedSize : Int) (msg : CheckInAllocMsg) : Except AccessError Unit :=
  if (!fitsI64Mirror signedSize) = true then
    Except.error (AccessError.signedSizeOutsideI64 signedSize)
  else
    let inBounds : Prop :=
      if signedSize ≥ 0 then
        offset.bytes.toNat + signedSize.toNat ≤ allocSize.bytes.toNat
      else
        let amount := (Int.neg signedSize).toNat
        (decide (amount ≤ offset.bytes.toNat) &&
          decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = true
    if (!decide inBounds) = true then
      Except.bind (Except.mapError AccessError.pointerArithmetic
          (target.signExtendToTargetIsize offset.bytes)) fun signedOffset =>
        Except.error (AccessError.pointerOutOfBounds id allocSize
          signedOffset.toInt signedSize msg)
    else Except.ok ()

private theorem checkedBounds_eq_mirror (target : PointerArithmetic)
    (id : Miri.Memory.AllocId) (allocSize offset : Size)
    (signedSize : Int) (msg : CheckInAllocMsg) :
    checkedBounds target id allocSize offset signedSize msg =
      checkedBoundsMirror target id allocSize offset signedSize msg := rfl

/-- Non-negative `Miri.Memory.checkedBounds` succeeds for any `sz < 2^63`
whenever `offset + sz ≤ allocSize` (agreeing with `MirSemantics.isInBounds`). -/
theorem checkedBounds_ofNat_inbounds (target : PointerArithmetic)
    (id : Miri.Memory.AllocId) (allocSize offset : Size) (sz : Nat)
    (msg : CheckInAllocMsg)
    (h_sz : sz < Nat.pow 2 63)
    (h_in : offset.bytes.toNat + sz ≤ allocSize.bytes.toNat) :
    checkedBounds target id allocSize offset (Int.ofNat sz) msg = .ok () := by
  rw [checkedBounds_eq_mirror]
  dsimp only [checkedBoundsMirror]
  rw [fitsI64Mirror_ofNat h_sz, Bool.not_true, ite_false_eq]
  have h_ge0 : (0 : Int) ≤ Int.ofNat sz := Int.natCast_nonneg sz
  have h_dec :
      decide (if Int.ofNat sz ≥ 0 then
          offset.bytes.toNat + (Int.ofNat sz).toNat ≤ allocSize.bytes.toNat
        else
          (decide ((Int.neg (Int.ofNat sz)).toNat ≤ offset.bytes.toNat) &&
            decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = true) =
        true :=
    decide_eq_true (by rw [ite_pos_eq h_ge0]; exact h_in)
  rw [h_dec, Bool.not_true, ite_false_eq]

/-- Non-negative `Miri.Memory.checkedBounds` faults with `.pointerOutOfBounds`
when `allocSize < offset + sz` (with `sz < 2^63` on 64-bit `ptrArith64`). -/
theorem checkedBounds_ofNat_oob_64 (id : Miri.Memory.AllocId)
    (allocSize offset : Size) (sz : Nat) (msg : CheckInAllocMsg)
    (h_sz : sz < Nat.pow 2 63)
    (h_oob : allocSize.bytes.toNat < offset.bytes.toNat + sz) :
    ∃ signedOff : Int64,
      ptrArith64.signExtendToTargetIsize offset.bytes = .ok signedOff ∧
      checkedBounds ptrArith64 id allocSize offset (Int.ofNat sz) msg =
        .error (.pointerOutOfBounds id allocSize signedOff.toInt
          (Int.ofNat sz) msg) := by
  let ⟨signedOff, h_se⟩ := ptrArith64_signExtendToTargetIsize_ok offset.bytes
  refine ⟨signedOff, h_se, ?_⟩
  rw [checkedBounds_eq_mirror]
  dsimp only [checkedBoundsMirror]
  rw [fitsI64Mirror_ofNat h_sz, Bool.not_true, ite_false_eq]
  have h_ge0 : (0 : Int) ≤ Int.ofNat sz := Int.natCast_nonneg sz
  have h_dec :
      decide (if Int.ofNat sz ≥ 0 then
          offset.bytes.toNat + (Int.ofNat sz).toNat ≤ allocSize.bytes.toNat
        else
          (decide ((Int.neg (Int.ofNat sz)).toNat ≤ offset.bytes.toNat) &&
            decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = true) =
        false :=
    decide_eq_false (by rw [ite_pos_eq h_ge0]; exact Nat.not_le.2 h_oob)
  rw [h_dec, Bool.not_false, ite_true_eq, h_se]
  rfl

/-- Negative-size `Miri.Memory.checkedBounds` rejects any signed size strictly
below `i64::MIN` (`Int.negSucc k` with `2^63 - 1 < k`) with
`.signedSizeOutsideI64`. -/
theorem checkedBounds_negSucc_outsideI64_err (target : PointerArithmetic)
    (id : Miri.Memory.AllocId) (allocSize offset : Size) (k : Nat)
    (msg : CheckInAllocMsg)
    (hk : 9223372036854775807 < k) :
    checkedBounds target id allocSize offset (Int.negSucc k) msg =
      .error (.signedSizeOutsideI64 (Int.negSucc k)) := by
  rw [checkedBounds_eq_mirror]
  dsimp only [checkedBoundsMirror]
  rw [fitsI64Mirror_negSucc_outside hk]
  rfl

/-- Negative-size `Miri.Memory.checkedBounds` succeeds for `Int.negSucc k`
(`-(k + 1) ≥ -2^63`) whenever `k + 1 ≤ offset ≤ allocSize`. -/
theorem checkedBounds_negSucc_inbounds (target : PointerArithmetic)
    (id : Miri.Memory.AllocId) (allocSize offset : Size) (k : Nat)
    (msg : CheckInAllocMsg)
    (hk : k ≤ 9223372036854775807)
    (h_lo : k + 1 ≤ offset.bytes.toNat)
    (h_hi : offset.bytes.toNat ≤ allocSize.bytes.toNat) :
    checkedBounds target id allocSize offset (Int.negSucc k) msg = .ok () := by
  rw [checkedBounds_eq_mirror]
  dsimp only [checkedBoundsMirror]
  rw [fitsI64Mirror_negSucc hk, Bool.not_true, ite_false_eq]
  have h_nge0 : ¬ (Int.negSucc k ≥ 0) :=
    Int.not_le.2 (Int.negSucc_lt_zero k)
  have h_neg_toNat : (Int.neg (Int.negSucc k)).toNat = k + 1 := rfl
  have h_true :
      (decide ((Int.neg (Int.negSucc k)).toNat ≤ offset.bytes.toNat) &&
        decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = true := by
    rw [h_neg_toNat, decide_eq_true h_lo, decide_eq_true h_hi]
    rfl
  have h_dec :
      decide (if Int.negSucc k ≥ 0 then
          offset.bytes.toNat + (Int.negSucc k).toNat ≤ allocSize.bytes.toNat
        else
          (decide ((Int.neg (Int.negSucc k)).toNat ≤ offset.bytes.toNat) &&
            decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = true) =
        true :=
    decide_eq_true (by rw [ite_neg_eq h_nge0]; exact h_true)
  rw [h_dec, Bool.not_true, ite_false_eq]

/-- Negative-size `Miri.Memory.checkedBounds` faults with `.pointerOutOfBounds`
when `offset < k + 1` (backward underflow) or `allocSize < offset` on 64-bit
`ptrArith64`. -/
theorem checkedBounds_negSucc_oob_64 (id : Miri.Memory.AllocId)
    (allocSize offset : Size) (k : Nat) (msg : CheckInAllocMsg)
    (hk : k ≤ 9223372036854775807)
    (h_oob : offset.bytes.toNat < k + 1 ∨
      allocSize.bytes.toNat < offset.bytes.toNat) :
    ∃ signedOff : Int64,
      ptrArith64.signExtendToTargetIsize offset.bytes = .ok signedOff ∧
      checkedBounds ptrArith64 id allocSize offset (Int.negSucc k) msg =
        .error (.pointerOutOfBounds id allocSize signedOff.toInt
          (Int.negSucc k) msg) := by
  let ⟨signedOff, h_se⟩ := ptrArith64_signExtendToTargetIsize_ok offset.bytes
  refine ⟨signedOff, h_se, ?_⟩
  rw [checkedBounds_eq_mirror]
  dsimp only [checkedBoundsMirror]
  rw [fitsI64Mirror_negSucc hk, Bool.not_true, ite_false_eq]
  have h_nge0 : ¬ (Int.negSucc k ≥ 0) :=
    Int.not_le.2 (Int.negSucc_lt_zero k)
  have h_neg_toNat : (Int.neg (Int.negSucc k)).toNat = k + 1 := rfl
  have h_false :
      (decide ((Int.neg (Int.negSucc k)).toNat ≤ offset.bytes.toNat) &&
        decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = false := by
    rw [h_neg_toNat]
    cases h_oob with
    | inl h1 =>
      rw [decide_eq_false (Nat.not_le.2 h1)]
      rfl
    | inr h2 =>
      rw [decide_eq_false (Nat.not_le.2 h2), Bool.and_false]
  have h_dec :
      decide (if Int.negSucc k ≥ 0 then
          offset.bytes.toNat + (Int.negSucc k).toNat ≤ allocSize.bytes.toNat
        else
          (decide ((Int.neg (Int.negSucc k)).toNat ≤ offset.bytes.toNat) &&
            decide (offset.bytes.toNat ≤ allocSize.bytes.toNat)) = true) =
        false :=
    decide_eq_false (by rw [ite_neg_eq h_nge0, h_false]; intro h; cases h)
  rw [h_dec, Bool.not_false, ite_true_eq, h_se]
  rfl

private def checkAndDerefPtrMirror {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (msg : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : LiveAllocationLookup) :
    Except AccessError (Option (CheckedPointerAccess ProvExtra)) :=
  if (!fitsI64Mirror signedSize) = true then
    Except.error (AccessError.signedSizeOutsideI64 signedSize)
  else if (signedSize == 0) = true then
    Except.ok none
  else
    match resolve ptr signedSize with
    | Except.ok resolved =>
      match lookup resolved.allocId with
      | Except.ok info =>
        if (info.kind == AllocationKind.dead) = true then
          Except.error (AccessError.allocationLookup
            (AllocationLookupError.deadAllocation resolved.allocId))
        else
          Except.bind (checkedBounds target resolved.allocId info.size
              resolved.offset signedSize msg) fun _ =>
            Except.ok (some (CheckedPointerAccess.mk resolved info))
      | Except.error (AllocationLookupError.deadAllocation id) =>
        Except.error (AccessError.allocationLookup
          (AllocationLookupError.deadAllocation id))
      | Except.error (AllocationLookupError.unavailable id) =>
        Except.error (AccessError.allocationLookup
          (AllocationLookupError.unavailable id))
    | Except.error address =>
      Except.error (AccessError.danglingIntegerPointer address signedSize msg)

private theorem checkAndDerefPtr_eq_mirror {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int) (msg : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : LiveAllocationLookup) :
    checkAndDerefPtr target ptr signedSize msg resolve lookup =
      checkAndDerefPtrMirror target ptr signedSize msg resolve lookup := rfl

/-- Exact characterization of `Miri.Memory.checkAndDerefPtr` for nonzero
in-bounds accesses on live allocations. -/
theorem checkAndDerefPtr_nonzero_ok {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (sz : Nat) (msg : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup)
    (resolved : ResolvedPointer ProvExtra) (info : AllocationInfo)
    (h_pos : 0 < sz) (h_sz : sz < Nat.pow 2 63)
    (h_res : resolve ptr (Int.ofNat sz) = .ok resolved)
    (h_lk : lookup resolved.allocId = .ok info)
    (h_live : info.kind ≠ .dead)
    (h_in : resolved.offset.bytes.toNat + sz ≤ info.size.bytes.toNat) :
    checkAndDerefPtr target ptr (Int.ofNat sz) msg resolve lookup =
      .ok (some ⟨resolved, info⟩) := by
  rw [checkAndDerefPtr_eq_mirror]
  dsimp only [checkAndDerefPtrMirror]
  have h_ne0 : (Int.ofNat sz == 0) = false := by
    cases sz with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_pos)
    | succ _ => rfl
  have h_ndead : (info.kind == .dead) = false := by
    cases h_eq : (info.kind == .dead) with
    | false => rfl
    | true => exact False.elim (h_live (eq_of_beq h_eq))
  rw [fitsI64Mirror_ofNat h_sz, Bool.not_true, ite_false_eq, h_ne0,
    ite_false_eq, h_res]
  dsimp only
  rw [h_lk]
  dsimp only
  rw [h_ndead, ite_false_eq]
  rw [checkedBounds_ofNat_inbounds target resolved.allocId info.size
    resolved.offset sz msg h_sz h_in]
  rfl

/-- Exact characterization of `Miri.Memory.checkAndDerefPtr` rejecting a
dangling integer pointer (`resolve = .error addr`) on any nonzero access. -/
theorem checkAndDerefPtr_nonzero_dangling_err {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (sz : Nat) (msg : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup)
    (addr : UInt64)
    (h_pos : 0 < sz) (h_sz : sz < Nat.pow 2 63)
    (h_res : resolve ptr (Int.ofNat sz) = .error addr) :
    checkAndDerefPtr target ptr (Int.ofNat sz) msg resolve lookup =
      .error (.danglingIntegerPointer addr (Int.ofNat sz) msg) := by
  rw [checkAndDerefPtr_eq_mirror]
  dsimp only [checkAndDerefPtrMirror]
  have h_ne0 : (Int.ofNat sz == 0) = false := by
    cases sz with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_pos)
    | succ _ => rfl
  rw [fitsI64Mirror_ofNat h_sz, Bool.not_true, ite_false_eq, h_ne0,
    ite_false_eq, h_res]

/-- Dead-allocation lookup characterization in `Miri.Memory.MemoryState`: when
`id` is absent from live, function-pointer, va-list, and global tables and
present in `st.dead`, `st.getAllocInfo id` returns `.ok ⟨..., .dead, .Not⟩`. -/
theorem miriMemoryState_getAllocInfo_dead {Prov Extra MachineKind : Type}
    (st : Miri.Memory.MemoryState Prov Extra MachineKind)
    (id : Miri.Memory.AllocId) (deadEntry : DeadAllocation)
    (h_live : st.live.find? (fun entry => entry.1 == id) = none)
    (h_fn : st.hasFunctionPointer id = false)
    (h_va : st.hasVaListId id = false)
    (h_gl : st.findGlobal? id = none)
    (h_dead : st.dead.find? (fun entry => entry.allocId == id) =
      some deadEntry) :
    st.getAllocInfo id = .ok ⟨deadEntry.size, deadEntry.align, .dead, .Not⟩
    := by
  unfold Miri.Memory.MemoryState.getAllocInfo
  have h_va' : st.hasVaListId id = false := h_va
  dsimp only [Miri.Memory.MemoryState.hasVaListId] at h_va'
  rw [h_live, h_fn, h_va', h_gl, h_dead]
  rfl

/-- Miri-side dead-allocation access error (paired with `deallocateStack_spec`):
any nonzero `checkAndDerefPtr` resolving to a dead allocation (`info.kind =
.dead`, as returned by `MemoryState.getAllocInfo` on `dead` entries, or
`lookup = .error (.deadAllocation _)`) faults with
`.error (.allocationLookup (.deadAllocation resolved.allocId))`. -/
theorem checkAndDerefPtr_nonzero_dead_err {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (sz : Nat) (msg : CheckInAllocMsg)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup)
    (resolved : ResolvedPointer ProvExtra)
    (h_pos : 0 < sz) (h_sz : sz < Nat.pow 2 63)
    (h_res : resolve ptr (Int.ofNat sz) = .ok resolved)
    (h_dead :
      (∃ info : AllocationInfo,
        lookup resolved.allocId = .ok info ∧ info.kind = .dead) ∨
      lookup resolved.allocId = .error (.deadAllocation resolved.allocId)) :
    checkAndDerefPtr target ptr (Int.ofNat sz) msg resolve lookup =
      .error (.allocationLookup (.deadAllocation resolved.allocId)) := by
  rw [checkAndDerefPtr_eq_mirror]
  dsimp only [checkAndDerefPtrMirror]
  have h_ne0 : (Int.ofNat sz == 0) = false := by
    cases sz with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_pos)
    | succ _ => rfl
  rw [fitsI64Mirror_ofNat h_sz, Bool.not_true, ite_false_eq, h_ne0,
    ite_false_eq, h_res]
  dsimp only
  cases h_dead with
  | inl h_info =>
    let ⟨info, h_lk, h_kind⟩ := h_info
    rw [h_lk]
    dsimp only
    rw [h_kind]
    rfl
  | inr h_err =>
    rw [h_err]

/-- Full 64-bit pointer-in-memory provenance round-trip: writing any
`Pointer Miri.Memory.Provenance` into an 8-byte mutable `fromBytes` allocation
via `Allocation.writePointer` and reading it back via
`Allocation.readScalar ... true` recovers the exact `Scalar.fromPointer`
(preserving both offset and provenance). -/
theorem miriAlloc_writePointer_readScalar_roundTrip
    (ptr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (extra : Miri.TreeBorrows.BorrowTree)
    (raw0 : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
    (h_fb0 : Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
      (Array.replicate 8 0) Align.EIGHT .Mut = .ok raw0) :
    let layout := RuntimeTargetDataLayout.default.base
    let range := allocRange Size.ZERO (Size.ofBytes 8)
    ∃ after,
      Miri.Memory.Allocation.writePointer layout range ptr
        (raw0.withExtra extra) = .ok () after ∧
      after.readScalar layout range true = .ok (Scalar.fromPointer layout ptr)
      := by
  intro layout range
  cases h_wp_res :
      Miri.Memory.Allocation.writePointer layout range ptr
        (raw0.withExtra extra) with
  | error e s =>
    dsimp only [Miri.Memory.Allocation.fromBytes] at h_fb0
    injection h_fb0 with h_mk0
    subst h_mk0
    have h_tub :
        targetUIntBytesMirror layout (Size.ofBytes 8)
          (BitVec.ofNat 128 ptr.offset.bytes.toNat) =
        .ok (beBytes ptr.offset.bytes.toNat 8 8) := by
      have h_be := targetUIntBytesMirror_be 8 (by decide)
        (BitVec.ofNat 128 ptr.offset.bytes.toNat)
      have h_bv :
          (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat =
            ptr.offset.bytes.toNat := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt
          (Nat.lt_trans (u64_toNat_lt_pow64 ptr.offset.bytes) (by decide))
      rw [h_bv] at h_be
      exact h_be
    let ⟨pm1, h_ins, _, _⟩ :=
      provenanceMap_new_insertPtr_roundTrip (Prov := Miri.Memory.Provenance)
        Size.ZERO (Size.ofBytes 8) ptr.provenance (by decide) (by decide)
    have h_data_sz : (beBytes ptr.offset.bytes.toNat 8 8).size = 8 :=
      beBytes_size _ 8 8
    have h_splice_eq :
        (Array.replicate 8 (0 : UInt8)).extract 0 0 ++
          beBytes ptr.offset.bytes.toNat 8 8 ++
          (Array.replicate 8 (0 : UInt8)).extract 8
            (Array.replicate 8 (0 : UInt8)).size =
        beBytes ptr.offset.bytes.toNat 8 8 := by
      have h_e1 : (Array.replicate 8 (0 : UInt8)).extract 0 0 = Array.mk [] :=
        rfl
      have h_e2 :
          (Array.replicate 8 (0 : UInt8)).extract 8
            (Array.replicate 8 (0 : UInt8)).size = Array.mk [] := rfl
      rw [h_e1, h_e2, Array.empty_append, Array.append_empty]
    dsimp only [Miri.Memory.Allocation.writePointer,
      Miri.Memory.Allocation.writeScalar, Miri.Memory.Allocation.withExtra,
      Scalar.fromPointer, Scalar.toBitsOrPtrInternal, Id.run, bind, Bind.bind,
      pure, Pure.pure, layout, range] at h_wp_res
    rw [show (Miri.Memory.Mutability.Mut != Miri.Memory.Mutability.Mut) = false
      from rfl, ite_false_eq] at h_wp_res
    change
      (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
          (Size.ofBytes 8) (BitVec.ofNat 128 ptr.offset.bytes.toNat) with
       | Except.ok data => _
       | Except.error error => EStateM.Result.error error _) =
      EStateM.Result.error e s at h_wp_res
    rw [h_tub] at h_wp_res
    dsimp only [allocRange, Size.ZERO, Size.ofBytes] at h_wp_res
    have h_u0 : UInt64.toNat 0 = 0 := rfl
    have h_u8 : UInt64.toNat 8 = 8 := rfl
    have h_sz8 :
        (UInt64.ofNat (Array.replicate 8 (0 : UInt8)).size).toNat = 8 := rfl
    simp only [h_u0, h_u8, Nat.zero_add, h_splice_eq, h_data_sz, h_sz8]
      at h_wp_res
    rw [show (8 != 8) = false from rfl, ite_false_eq] at h_wp_res
    change
      (if (({ bytes := (8 : UInt64) } : Size) != Size.ofBytes 8) = true
       then _ else _) = EStateM.Result.error e s at h_wp_res
    rw [show (({ bytes := (8 : UInt64) } : Size) != Size.ofBytes 8) = false
      from rfl, ite_false_eq] at h_wp_res
    have h_ins_any : ∀ (sz : Size), sz = Size.ofBytes 8 →
        ProvenanceMap.insertPtr { bytes := 0 } ptr.provenance sz
          (ProvenanceMap.new (Prov := Miri.Memory.Provenance)) =
            .ok () pm1 := by
      intro sz hsz; rw [hsz]; exact h_ins
    dsimp only [ProvenanceMap.new, Option.map] at h_wp_res
    dsimp only [ProvenanceMap.new] at h_ins_any
    rw [h_ins_any] at h_wp_res
    · cases h_wp_res
    · rfl
  | ok u after =>
    dsimp only [Miri.Memory.Allocation.fromBytes] at h_fb0
    injection h_fb0 with h_mk0
    subst h_mk0
    have h_tub :
        targetUIntBytesMirror layout (Size.ofBytes 8)
          (BitVec.ofNat 128 ptr.offset.bytes.toNat) =
        .ok (beBytes ptr.offset.bytes.toNat 8 8) := by
      have h_be := targetUIntBytesMirror_be 8 (by decide)
        (BitVec.ofNat 128 ptr.offset.bytes.toNat)
      have h_bv :
          (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat =
            ptr.offset.bytes.toNat := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt
          (Nat.lt_trans (u64_toNat_lt_pow64 ptr.offset.bytes) (by decide))
      rw [h_bv] at h_be
      exact h_be
    have h_rtu :
        readTargetUIntMirror layout (beBytes ptr.offset.bytes.toNat 8 8) =
        .ok (BitVec.ofNat 128 ptr.offset.bytes.toNat) := by
      have h_rd :=
        readTargetUIntMirror_be 8 (by decide) ptr.offset.bytes.toNat
      have h_mod :
          HMod.hMod ptr.offset.bytes.toNat (HPow.hPow 2 (8 * 8)) =
            ptr.offset.bytes.toNat :=
        Nat.mod_eq_of_lt (u64_toNat_lt_pow64 ptr.offset.bytes)
      rw [h_mod] at h_rd
      exact h_rd
    let ⟨pm1, h_ins, _, h_rptr⟩ :=
      provenanceMap_new_insertPtr_roundTrip (Prov := Miri.Memory.Provenance)
        Size.ZERO (Size.ofBytes 8) ptr.provenance (by decide) (by decide)
    have h_data_sz : (beBytes ptr.offset.bytes.toNat 8 8).size = 8 :=
      beBytes_size _ 8 8
    have h_splice_eq :
        (Array.replicate 8 (0 : UInt8)).extract 0 0 ++
          beBytes ptr.offset.bytes.toNat 8 8 ++
          (Array.replicate 8 (0 : UInt8)).extract 8
            (Array.replicate 8 (0 : UInt8)).size =
        beBytes ptr.offset.bytes.toNat 8 8 := by
      have h_e1 : (Array.replicate 8 (0 : UInt8)).extract 0 0 = Array.mk [] :=
        rfl
      have h_e2 :
          (Array.replicate 8 (0 : UInt8)).extract 8
            (Array.replicate 8 (0 : UInt8)).size = Array.mk [] := rfl
      rw [h_e1, h_e2, Array.empty_append, Array.append_empty]
    have h_wp_eq := h_wp_res
    dsimp only [Miri.Memory.Allocation.writePointer,
      Miri.Memory.Allocation.writeScalar, Miri.Memory.Allocation.withExtra,
      Scalar.fromPointer, Scalar.toBitsOrPtrInternal, Id.run, bind, Bind.bind,
      pure, Pure.pure, layout, range] at h_wp_eq
    rw [show (Miri.Memory.Mutability.Mut != Miri.Memory.Mutability.Mut) = false
      from rfl, ite_false_eq] at h_wp_eq
    change
      (match targetUIntBytesMirror RuntimeTargetDataLayout.default.base
          (Size.ofBytes 8) (BitVec.ofNat 128 ptr.offset.bytes.toNat) with
       | Except.ok data => _
       | Except.error error => EStateM.Result.error error _) =
      EStateM.Result.ok u after at h_wp_eq
    rw [h_tub] at h_wp_eq
    dsimp only [allocRange, Size.ZERO, Size.ofBytes] at h_wp_eq
    have h_u0 : UInt64.toNat 0 = 0 := rfl
    have h_u8 : UInt64.toNat 8 = 8 := rfl
    have h_sz8 :
        (UInt64.ofNat (Array.replicate 8 (0 : UInt8)).size).toNat = 8 := rfl
    simp only [h_u0, h_u8, Nat.zero_add, h_splice_eq, h_data_sz, h_sz8]
      at h_wp_eq
    rw [show (8 != 8) = false from rfl, ite_false_eq] at h_wp_eq
    change
      (if (({ bytes := (8 : UInt64) } : Size) != Size.ofBytes 8) = true
       then _ else _) = EStateM.Result.ok u after at h_wp_eq
    rw [show (({ bytes := (8 : UInt64) } : Size) != Size.ofBytes 8) = false
      from rfl, ite_false_eq] at h_wp_eq
    have h_ins_any : ∀ (sz : Size), sz = Size.ofBytes 8 →
        ProvenanceMap.insertPtr { bytes := 0 } ptr.provenance sz
          (ProvenanceMap.new (Prov := Miri.Memory.Provenance)) =
            .ok () pm1 := by
      intro sz hsz; rw [hsz]; exact h_ins
    dsimp only [ProvenanceMap.new, Option.map] at h_wp_eq
    dsimp only [ProvenanceMap.new] at h_ins_any
    rw [h_ins_any] at h_wp_eq
    · injection h_wp_eq with _ h_after_mk
      refine ⟨after, rfl, ?_⟩
      subst h_after_mk
      dsimp only [Miri.Memory.Allocation.readScalar, bind, Bind.bind,
        Except.bind, pure, Pure.pure, Except.pure, layout, range]
      change
        (match checkedSliceMirror (beBytes ptr.offset.bytes.toNat 8 8)
            (Size.ofBytes 8) (allocRange Size.ZERO (Size.ofBytes 8)) with
         | Except.error e => Except.error e
         | Except.ok bs => _) = _
      have h_ext_self :
          (beBytes ptr.offset.bytes.toNat 8 8).extract 0 8 =
            beBytes ptr.offset.bytes.toNat 8 8 := by
        apply Array.toList_inj.mp
        rw [array_extract_toList, Nat.sub_zero, List.drop_zero]
        exact List.take_of_length_le
          (by rw [Array.length_toList, h_data_sz]; exact Nat.le_refl _)
      have h_cs :
          checkedSliceMirror (beBytes ptr.offset.bytes.toNat 8 8)
            (Size.ofBytes 8) (allocRange Size.ZERO (Size.ofBytes 8)) =
          .ok (beBytes ptr.offset.bytes.toNat 8 8) := by
        dsimp only [checkedSliceMirror]
        rw [h_data_sz,
          show (8 != (Size.ofBytes 8).bytes.toNat) = false from rfl,
          ite_false_eq]
        dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
        change
          Except.ok ((beBytes ptr.offset.bytes.toNat 8 8).extract 0 8) = _
        rw [h_ext_self]
      rw [h_cs]
      dsimp only
      -- Rewrite the slice first: converting the private `readTargetUInt` to
      -- its mirror is then cheap, while leaving the `extract` in place makes
      -- the conversion check evaluate the read on `beBytes`.
      have h_ext_rng :
          (beBytes ptr.offset.bytes.toNat 8 8).extract
              (allocRange Size.ZERO (Size.ofBytes 8)).start.bytes.toNat
              (UInt64.toNat (Size.bytes (Size.ofBytes
                ((allocRange Size.ZERO (Size.ofBytes 8)).start.bytes +
                  (allocRange Size.ZERO (Size.ofBytes 8)).size.bytes)))) =
            beBytes ptr.offset.bytes.toNat 8 8 :=
        h_ext_self
      rw [h_ext_rng]
      change
        (Except.bind (readTargetUIntMirror RuntimeTargetDataLayout.default.base
          (beBytes ptr.offset.bytes.toNat 8 8)) _) = _
      rw [h_rtu]
      dsimp only [Except.bind]
      rw [ite_true_eq]
      change (if (Size.ofBytes 8 != Size.ofBytes 8) = true then _ else _) = _
      rw [show (Size.ofBytes 8 != Size.ofBytes 8) = false from rfl,
        ite_false_eq]
      dsimp only [allocRange]
      have h_rptr_any : ∀ (sz : Size), sz = Size.ofBytes 8 →
          pm1.readPtr Size.ZERO sz = .ok (some ptr.provenance) := by
        intro sz hsz; rw [hsz]; exact h_rptr
      rw [h_rptr_any]
      · dsimp only
        have h_bv :
            (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat =
              ptr.offset.bytes.toNat := by
          rw [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt
            (Nat.lt_trans (u64_toNat_lt_pow64 ptr.offset.bytes) (by decide))
        have h_nmax :
            ¬ (18446744073709551615 <
                (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat) := by
          rw [h_bv]
          exact Nat.not_lt.mpr
            (Nat.le_pred_of_lt (u64_toNat_lt_pow64 ptr.offset.bytes))
        rw [ite_neg_eq h_nmax, h_bv]
        have h_u : UInt64.ofNat ptr.offset.bytes.toNat = ptr.offset.bytes :=
          u64_eq_of_toNat_eq
            (u64_ofNat_toNat_of_lt (u64_toNat_lt_pow64 ptr.offset.bytes))
        rw [h_u]
        rfl
      · rfl
    · rfl

/-! ## Section 7: Concrete End-to-End Non-Vacuity Witnesses -/

/-- Witness 1 (Miri nonzero-aligned zero-sized pointer check agreeing with
`MirSemantics.readBytes` at `size = 0`): in Miri, a 4-byte-aligned zero-sized
place (`alignLog2 = 2`, `size = 0`) skips dereference in `checkAndDerefPtr`
(`0 = .ok none`), passes `checkPtrAlign` at aligned offset `0`, and fails
`checkPtrAlign` at misaligned offset `1`. `MirSemantics.readBytes` on a
4-byte-aligned allocation agrees: `.ok []` at offset `0`
(`readBytes_zero_size`) and `.undefined` at offset `1`
(`readBytes_zero_size_misaligned`). -/
theorem witness_miri_zst_alignment_check :
    let prov : Miri.Memory.Provenance :=
      Miri.Memory.Provenance.concrete ⟨1, by decide⟩ BorTag.one
    let ptr0 : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Size.ZERO, some prov⟩
    let ptr1 : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Size.ofBytes 1, some prov⟩
    let resolve : PointerResolver Miri.Memory.Provenance Unit :=
      fun p _ => .ok ⟨⟨1, by decide⟩, p.offset, ()⟩
    let lookup : LiveAllocationLookup :=
      fun _ => .ok ⟨Size.ZERO, ⟨2⟩, .liveData, .Mut⟩
    checkAndDerefPtr ptrArith64 ptr1 0 .memoryAccess resolve lookup =
      .ok none ∧
    checkPtrAlign ptr0 ⟨2⟩ true resolve lookup (fun _ _ _ _ _ => none) =
      .ok () ∧
    checkPtrAlign ptr1 ⟨2⟩ true resolve lookup (fun _ _ _ _ _ => none) =
      .error (.alignmentCheckFailed
        ⟨Align.maxAlignedFactor (Size.ofBytes 1), ⟨2⟩⟩) ∧
    readBytes
      { nextAllocId := 2
        allocations :=
          [{ allocId := 1, alignLog2 := 2, mutability := .mut, bytes := [] }] }
      ⟨1, 0⟩ 0 2 = .ok [] ∧
    readBytes
      { nextAllocId := 2
        allocations :=
          [{ allocId := 1, alignLog2 := 2, mutability := .mut, bytes := [] }] }
      ⟨1, 1⟩ 0 2 = .error .undefined := by
  intro prov ptr0 ptr1 resolve lookup
  have h0 := checkPtrAlign_addrProv_of_resolved ptr0 2 (by decide) (by decide)
    resolve lookup ⟨⟨1, by decide⟩, Size.ZERO, ()⟩
    ⟨Size.ZERO, ⟨2⟩, .liveData, .Mut⟩ rfl rfl (by decide)
  have h1 := checkPtrAlign_addrProv_of_resolved ptr1 2 (by decide) (by decide)
    resolve lookup ⟨⟨1, by decide⟩, Size.ofBytes 1, ()⟩
    ⟨Size.ZERO, ⟨2⟩, .liveData, .Mut⟩ rfl rfl (by decide)
  exact ⟨rfl, h0.1 (by decide), h1.2 (by decide),
    readBytes_zero_size _ ⟨1, 0⟩ 2 _ rfl rfl,
    readBytes_zero_size_misaligned _ ⟨1, 1⟩ 2 _ rfl rfl⟩

/-- Witness 2 (Coexistence of tracked caller slices in `CallerMemory` and
`Miri.Memory.MemoryState` alongside a deallocated dead stack slot, a live
indirect stack slot, and an uninitialized `allocateStack` slot in the same
`MirSemantics.MemoryState`): mutating tracked slice `1` in lockstep via
`MirSemantics.writeBytes` and `MemoryState.setLiveAllocation` updates slice `1`
to `[10, 77, 66, 40]`, preserves shared slice `2` (`[99, 88]`), preserves the
live/dead/uninit stack allocations, and rejects writes to shared slice `2`. -/
theorem witness_trackedSlice_stack_and_dead_coexistence :
    let a1 : MirSemantics.Allocation := {
      allocId := 1, alignLog2 := 0, mutability := .mut,
      bytes := [10, 20, 30, 40].map (fun b => AllocByte.init b none),
      live := true
    }
    let a2 : MirSemantics.Allocation := {
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := [99, 88].map (fun b => AllocByte.init b none),
      live := true
    }
    let cm0 : CallerMemory := ⟨[a1, a2]⟩
    let a1' : MirSemantics.Allocation := {
      a1 with
      bytes := [10, 77, 66, 40].map (fun b => AllocByte.init b none)
    }
    let cm1 : CallerMemory := ⟨replaceAllocation a1' cm0.allocations⟩
    let m0 : MirSemantics.MemoryState :=
      { nextAllocId := 3, allocations := [a1, a2] }
    let (m_s1, p_dead) := allocateStack m0 (intLayout .i32)
    let (m_s2, p_live) := allocateStack m_s1 (intLayout .i32)
    let (m_s3, p_uninit) := allocateStack m_s2 (intLayout .i32)
    let v42 := Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 42)⟩
    ∃ (m_st m_de m_fin : MirSemantics.MemoryState)
      (miriMem0 miriMem1 : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit)
      (ma1 ma1' ma2 : Miri.Memory.Allocation Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree),
      storeIndirect m_s3 (.int .i32 false) p_live v42 = .ok m_st ∧
      deallocateStack m_st p_dead = .ok m_de ∧
      CallerMemorySliceRel cm0 [1, 2] m_de miriMem0 ∧
      writeBytes m_de ⟨1, 1⟩ 0 ([77, 66].map (fun b => AllocByte.init b none)) =
        .ok m_fin ∧
      Miri.Memory.Allocation.writeBytes (Size.ofBytes 1) (Array.mk [77, 66])
        (Size.ofBytes 8) ma1 = .ok () ma1' ∧
      miriMem0.setLiveAllocation ⟨1, by decide⟩ ma1' = .ok miriMem1 ∧
      CallerMemorySliceRel cm1 [1, 2] m_fin miriMem1 ∧
      findAllocation 1 cm1.allocations = some a1' ∧
      findAllocation 2 cm1.allocations = some a2 ∧
      readBytes m_fin ⟨1, 0⟩ 4 0 =
        .ok ([10, 77, 66, 40].map (fun b => AllocByte.init b none)) ∧
      ma1'.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) =
        .ok (Array.mk [10, 77, 66, 40]) ∧
      readBytes m_fin ⟨2, 0⟩ 2 0 =
        .ok ([99, 88].map (fun b => AllocByte.init b none)) ∧
      ma2.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) =
        .ok (Array.mk [99, 88]) ∧
      loadIndirect m_fin (.int .i32 false) p_live = .ok (some v42) ∧
      loadIndirect m_fin (.int .i32 false) p_uninit = .ok none ∧
      loadIndirect m_fin (.int .i32 false) p_dead = .error .undefined ∧
      writeBytes m_fin ⟨2, 0⟩ 0 ([1].map (fun b => AllocByte.init b none)) =
        .error .undefined ∧
      Miri.Memory.Allocation.writeBytes Size.ZERO (Array.mk [1])
        (Size.ofBytes 8) ma2 = .error .readOnlyAllocation ma2 := by
  intro a1 a2 cm0 a1' cm1 m0
  dsimp only
  let s1 := allocateStack m0 (intLayout .i32)
  let s2 := allocateStack s1.1 (intLayout .i32)
  let s3 := allocateStack s2.1 (intLayout .i32)
  let p_dead := s1.2
  let p_live := s2.2
  let p_uninit := s3.2
  let v42 := Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 42)⟩
  let t1 := Miri.TreeBorrows.BorrowTree.new BorTag.one (Size.ofBytes 4)
  let t2 := Miri.TreeBorrows.BorrowTree.new BorTag.one (Size.ofBytes 2)
  let ⟨ma1, h_rel1⟩ := allocByteSliceRel_of_initBytes
    1 0 .mut [10, 20, 30, 40] t1 (by decide) (by decide)
  let ⟨ma2, h_rel2⟩ := allocByteSliceRel_of_initBytes
    2 0 .shared [99, 88] t2 (by decide) (by decide)
  let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
  let id2 : Miri.Memory.AllocId := ⟨2, by decide⟩
  let miriMem0 : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit := {
    Miri.Memory.MemoryState.empty
      (Prov := Miri.Memory.Provenance)
      (Extra := Miri.TreeBorrows.BorrowTree)
      (MachineKind := Unit) with
    nextAllocId := 3
    live := Array.mk [(id1, ⟨.stack, ma1⟩), (id2, ⟨.stack, ma2⟩)]
  }
  have h_fr0 : MemoryAllIdsLt m0 := by
    intro b hb
    cases hb with
    | head => decide
    | tail _ hb2 =>
      cases hb2 with
      | head => decide
      | tail _ hb3 => cases hb3
  have h_tr0 : TrackedSliceMemRel [1, 2] m0 miriMem0 := by
    intro id h_in
    cases h_in with
    | head =>
      refine ⟨by decide, by decide, by decide, a1, [10, 20, 30, 40], id1,
        ⟨.stack, ma1⟩, rfl, rfl, ?_, h_rel1⟩
      rw [← Array.find?_toList]
      rfl
    | tail _ h_in2 =>
      cases h_in2 with
      | head =>
        refine ⟨by decide, by decide, by decide, a2, [99, 88], id2,
          ⟨.stack, ma2⟩, rfl, rfl, ?_, h_rel2⟩
        rw [← Array.find?_toList]
        rfl
      | tail _ h_nil => cases h_nil
  let ⟨h_untr1, h_fr1, h_tr1⟩ :=
    trackedSliceMemRel_allocateStack (intLayout .i32) h_fr0 h_tr0
  let ⟨h_untr2, h_fr2, h_tr2⟩ :=
    trackedSliceMemRel_allocateStack (intLayout .i32) h_fr1 h_tr1
  let ⟨_, h_fr3, h_tr3⟩ :=
    trackedSliceMemRel_allocateStack (intLayout .i32) h_fr2 h_tr2
  have h_st_ex :
      ∃ m_st, storeIndirect s3.1 (.int .i32 false) p_live v42 = .ok m_st :=
    ⟨_, rfl⟩
  let ⟨m_st, h_st⟩ := h_st_ex
  let ⟨h_fr4, h_tr4⟩ :=
    trackedSliceMemRel_storeIndirect_untracked h_fr3 h_tr3 h_untr2 h_st
  have h_st_eq := h_st
  injection h_st_eq with h_mst_def
  have h_de_ex : ∃ m_de, deallocateStack m_st p_dead = .ok m_de := by
    rw [← h_mst_def]
    exact ⟨_, rfl⟩
  let ⟨m_de, h_de⟩ := h_de_ex
  let ⟨_, h_tr5⟩ :=
    trackedSliceMemRel_deallocateStack_untracked h_fr4 h_tr4 h_untr1 h_de
  have h_de_eq := h_de
  rw [← h_mst_def] at h_de_eq
  injection h_de_eq with h_mde_def
  have h_cm_de : CallerMemorySliceRel cm0 [1, 2] m_de miriMem0 := by
    refine ⟨h_tr5, ?_⟩
    intro id h_in
    rw [← h_mde_def]
    cases h_in with
    | head => rfl
    | tail _ h_in2 =>
      cases h_in2 with
      | head => rfl
      | tail _ h_nil => cases h_nil
  have h_fa1_de : findAllocation 1 m_de.allocations = some a1 := by
    rw [← h_mde_def]
    rfl
  let ⟨m_fin, mid_got, kind_got, ma1_got, ma1', miriMem1, h_mid_got,
      h_f0_got, h_f1_got, h_w1, _, h_mw1, h_set1, h_cm1, _, _⟩ :=
    trackedSliceMemRel_writeBytes_tracked_step h_cm_de
      (List.Mem.head [2]) h_fa1_de rfl 1 0 [77, 66] rfl (by decide)
  have h_mid_eq : mid_got = id1 := by
    cases mid_got with
    | mk v nz =>
      dsimp only at h_mid_got
      subst h_mid_got
      rfl
  subst h_mid_eq
  have h_ma1_eq : ma1_got = ma1 := by
    rw [← Array.find?_toList] at h_f0_got
    dsimp only [miriMem0, List.find?] at h_f0_got
    rw [beq_self_eq_true] at h_f0_got
    dsimp only at h_f0_got
    injection h_f0_got with h_pair
    injection h_pair with _ h_loc
    injection h_loc with _ h_a
    exact h_a.symm
  rw [h_ma1_eq] at h_mw1
  have h_w1_eq := h_w1
  rw [← h_mde_def] at h_w1_eq
  injection h_w1_eq with h_mfin_def
  let ⟨_, _, _, a1_fin, raw1', mid1_fin, entry1_fin, hm1_fin, hfa1_fin,
      hmf1_fin, h_rel1'⟩ :=
    h_cm1.1 1 (List.Mem.head [2])
  have h_mid1_eq : mid1_fin = id1 := by
    cases mid1_fin with
    | mk v nz =>
      dsimp only at hm1_fin
      subst hm1_fin
      rfl
  subst h_mid1_eq
  have h_entry1_eq : entry1_fin.allocation = ma1' := by
    rw [h_f1_got] at hmf1_fin
    injection hmf1_fin with h_p
    injection h_p with _ h_e
    exact congrArg (fun x => x.allocation) h_e.symm
  have h_a1_fin :
      a1_fin = {
        a1 with
        bytes := [10, 77, 66, 40].map (fun b => AllocByte.init b none)
      } := by
    have hf := hfa1_fin
    rw [← h_mfin_def] at hf
    injection hf with h_eq
    exact h_eq.symm
  have h_raw1'_eq : raw1' = [10, 77, 66, 40] := by
    have h_map := h_rel1'.2.2.2.1
    rw [h_a1_fin] at h_map
    dsimp only [a1] at h_map
    have h_inj :
        ∀ (xs ys : List UInt8),
          xs.map (fun b => AllocByte.init b none) =
            ys.map (fun b => AllocByte.init b none) →
          xs = ys := by
      intro xs
      induction xs with
      | nil =>
        intro ys h
        cases ys with
        | nil => rfl
        | cons _ _ => cases h
      | cons x xt ih =>
        intro ys h
        cases ys with
        | nil => cases h
        | cons y yt =>
          injection h with h_hd h_tl
          injection h_hd with h_b _
          rw [h_b, ih yt h_tl]
    exact (h_inj _ _ h_map).symm
  subst h_raw1'_eq
  rw [h_entry1_eq] at h_rel1'
  have h_fa2_fin : findAllocation 2 m_fin.allocations = some a2 := by
    rw [← h_mfin_def]
    rfl
  have h_aid1 : a1_fin.allocId = 1 :=
    congrArg MirSemantics.Allocation.allocId h_a1_fin
  have h_fa1_aid :
      findAllocation a1_fin.allocId m_fin.allocations = some a1_fin := by
    rw [h_aid1]
    exact hfa1_fin
  have h_al1_fin : MirSemantics.isAligned a1_fin 0 0 = true :=
    congrArg (fun x => MirSemantics.isAligned x 0 0) h_a1_fin
  let ⟨h_rd1, h_mgb1, _⟩ := allocByteSliceRel_readBytes_agree h_rel1'
    h_fa1_aid 0 4 0 (by decide) h_al1_fin RuntimeTargetDataLayout.default.base
  rw [h_aid1] at h_rd1
  let ⟨h_rd2, h_mgb2, _⟩ := allocByteSliceRel_readBytes_agree h_rel2
    h_fa2_fin 0 2 0 (by decide) rfl RuntimeTargetDataLayout.default.base
  let ⟨h_ro_a, h_ro_m⟩ := allocByteSliceRel_writeBytes_readonly_fault
    h_rel2 h_fa2_fin rfl 0 0 [1] (by intro h; cases h) (by decide)
  have h_li_live : loadIndirect m_fin (.int .i32 false) p_live =
      .ok (some v42) := by
    rw [← h_mfin_def]
    rfl
  have h_li_uninit : loadIndirect m_fin (.int .i32 false) p_uninit =
      .ok none := by
    rw [← h_mfin_def]
    rfl
  have h_li_dead : loadIndirect m_fin (.int .i32 false) p_dead =
      .error .undefined := by
    rw [← h_mfin_def]
    rfl
  exact ⟨m_st, m_de, m_fin, miriMem0, miriMem1, ma1, ma1', ma2,
    h_st, h_de, h_cm_de, h_w1, h_mw1, h_set1, h_cm1, rfl, rfl, h_rd1, h_mgb1,
    h_rd2, h_mgb2, h_li_live, h_li_uninit, h_li_dead, h_ro_a, h_ro_m⟩

private theorem empty_hashmap_contains_false (k : UInt64) :
    (EmptyCollection.emptyCollection :
      Std.HashMap UInt64 (Array Nat)).contains k = false := by
  have hc :
      (KeyedArray.empty (fun (x : UInt64) => x)).contains k = false := by
    rw [KeyedArray.contains_rows, ← Array.contains_toList, Array.toList_map]
    rfl
  exact hc

private theorem empty_hashmap_get?_none (k : UInt64) :
    (EmptyCollection.emptyCollection :
      Std.HashMap UInt64 (Array Nat)).get? k = none := by
  have hc := empty_hashmap_contains_false k
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  rw [Std.HashMap.get?_eq_getElem?]
  cases h :
      (EmptyCollection.emptyCollection :
        Std.HashMap UInt64 (Array Nat))[k]? with
  | none => rfl
  | some _ => rw [h] at hc; cases hc

private theorem keyedArray_empty_contains_false {V : Type}
    (f : V → UInt64) (k : UInt64) :
    (KeyedArray.empty f).contains k = false :=
  empty_hashmap_contains_false k

private theorem keyedArray_empty_any?_false {V : Type}
    (f : V → UInt64) (k : UInt64) (p : V → Bool) :
    (KeyedArray.empty f).any? k p = false := by
  dsimp only [KeyedArray.empty, KeyedArray.any?]
  rw [empty_hashmap_get?_none k]
  rfl

private theorem keyedArray_empty_find?_none {V : Type}
    (f : V → UInt64) (k : UInt64) :
    (KeyedArray.empty f).find? k = none := by
  dsimp only [KeyedArray.empty, KeyedArray.find?]
  rw [empty_hashmap_get?_none k]
  rfl

/-- Witness 3 (`MemoryState` stack allocation, indirect store/load round-trip,
and deallocation use-after-free paired with Miri's dead-allocation lookup
error). -/
theorem witness_indirect_stack_and_uaf :
    let (m1, p1) := allocateStack entryMemory (intLayout .i32)
    let (m2, p2) := allocateStack m1 (intLayout .i32)
    let v1 :=
      Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 305419896)⟩
    let v2 :=
      Val.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 42)⟩
    let deadId : Miri.Memory.AllocId := ⟨2, by decide⟩
    let deadMem : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit := {
      Miri.Memory.MemoryState.empty
        (Prov := Miri.Memory.Provenance)
        (Extra := Miri.TreeBorrows.BorrowTree)
        (MachineKind := Unit) with
      dead := Array.mk [⟨deadId, Size.ofBytes 4, ⟨2⟩⟩]
    }
    let deadPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Size.ZERO, some (.concrete deadId BorTag.one)⟩
    ∃ m3 m4 m5,
      storeIndirect m2 (.int .i32 false) p1 v1 = .ok m3 ∧
      storeIndirect m3 (.int .i32 false) p2 v2 = .ok m4 ∧
      loadIndirect m4 (.int .i32 false) p1 = .ok (some v1) ∧
      loadIndirect m4 (.int .i32 false) p2 = .ok (some v2) ∧
      deallocateStack m4 p1 = .ok m5 ∧
      loadIndirect m5 (.int .i32 false) p1 = .error .undefined ∧
      loadIndirect m5 (.int .i32 false) p2 = .ok (some v2) ∧
      checkAndDerefPtr ptrArith64 deadPtr 4 .memoryAccess
        Trusted.Correspondence.refResolvePointerPure deadMem.getAllocInfo =
        .error (.allocationLookup (.deadAllocation deadId)) := by
  dsimp only
  let deadId : Miri.Memory.AllocId := ⟨2, by decide⟩
  let deadMem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit := {
    Miri.Memory.MemoryState.empty
      (Prov := Miri.Memory.Provenance)
      (Extra := Miri.TreeBorrows.BorrowTree)
      (MachineKind := Unit) with
    dead := Array.mk [⟨deadId, Size.ofBytes 4, ⟨2⟩⟩]
  }
  let deadPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
    ⟨Size.ZERO, some (.concrete deadId BorTag.one)⟩
  have h_info : deadMem.getAllocInfo deadId =
      .ok ⟨Size.ofBytes 4, ⟨2⟩, .dead, .Not⟩ := by
    apply miriMemoryState_getAllocInfo_dead deadMem deadId
      ⟨deadId, Size.ofBytes 4, ⟨2⟩⟩
    · rw [← Array.find?_toList]; rfl
    · dsimp only [deadMem, Miri.Memory.MemoryState.empty,
        Miri.Memory.MemoryState.hasFunctionPointer]
      rw [keyedArray_empty_contains_false, keyedArray_empty_any?_false]
      rfl
    · dsimp only [deadMem, Miri.Memory.MemoryState.empty,
        Miri.Memory.MemoryState.hasVaListId]
      exact keyedArray_empty_contains_false _ _
    · dsimp only [deadMem, Miri.Memory.MemoryState.empty,
        Miri.Memory.MemoryState.findGlobal?]
      rw [keyedArray_empty_find?_none]
    · rw [← Array.find?_toList]
      dsimp only [deadMem, List.find?]
      rw [beq_self_eq_true]
  have h_uaf_miri := checkAndDerefPtr_nonzero_dead_err
    ptrArith64 deadPtr 4 .memoryAccess
    Trusted.Correspondence.refResolvePointerPure deadMem.getAllocInfo
    ⟨deadId, Size.ZERO, .concrete BorTag.one⟩ (by decide) (by decide) rfl
    (Or.inl ⟨⟨Size.ofBytes 4, ⟨2⟩, .dead, .Not⟩, h_info, rfl⟩)
  exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h_uaf_miri⟩

/-- Witness 4 (64-bit pointer offset, non-negative and negative `checkedBounds`
in-bounds & OOB, and `writePointer`/`readScalar` provenance round-trip). -/
theorem witness_ptr64_offset_bounds_and_provenance :
    let prov : Miri.Memory.Provenance :=
      Miri.Memory.Provenance.concrete ⟨7, by decide⟩ BorTag.one
    let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
      Pointer.new prov (Size.ofBytes 16)
    let layout := RuntimeTargetDataLayout.default.base
    let range := allocRange Size.ZERO (Size.ofBytes 8)
    ptr.wrappingOffset (Size.ofBytes 8) ptrArith64 =
      .ok (Pointer.new prov (Size.ofBytes 24)) ∧
    checkedBounds ptrArith64 ⟨7, by decide⟩ (Size.ofBytes 32)
      (Size.ofBytes 24) 8 .memoryAccess = .ok () ∧
    (∃ signedOff : Int64,
      checkedBounds ptrArith64 ⟨7, by decide⟩ (Size.ofBytes 32)
        (Size.ofBytes 24) 16 .memoryAccess =
        .error (.pointerOutOfBounds ⟨7, by decide⟩ (Size.ofBytes 32)
          signedOff.toInt 16 .memoryAccess)) ∧
    (∃ signedOffNeg : Int64,
      checkedBounds ptrArith64 ⟨7, by decide⟩ (Size.ofBytes 32)
        (Size.ofBytes 4) (Int.negSucc 7) .memoryAccess =
        .error (.pointerOutOfBounds ⟨7, by decide⟩ (Size.ofBytes 32)
          signedOffNeg.toInt (Int.negSucc 7) .memoryAccess)) ∧
    ∃ (raw0 : Miri.Memory.Allocation Miri.Memory.Provenance Unit)
      (after : Miri.Memory.Allocation Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.replicate 8 0) Align.EIGHT .Mut = .ok raw0 ∧
      Miri.Memory.Allocation.writePointer layout range ptr
        (raw0.withExtra
          (Miri.TreeBorrows.BorrowTree.new BorTag.one (Size.ofBytes 8))) =
        .ok () after ∧
      after.readScalar layout range true =
        .ok (Scalar.fromPointer layout ptr) := by
  intro prov ptr layout range
  have h_off := pointer_wrappingOffset_64 ptr (Size.ofBytes 8)
  have h_in := checkedBounds_ofNat_inbounds ptrArith64 ⟨7, by decide⟩
    (Size.ofBytes 32) (Size.ofBytes 24) 8 .memoryAccess (by decide) (by decide)
  let ⟨signedOff, _, h_oob⟩ := checkedBounds_ofNat_oob_64 ⟨7, by decide⟩
    (Size.ofBytes 32) (Size.ofBytes 24) 16 .memoryAccess
    (by decide) (by decide)
  let ⟨signedOffNeg, _, h_noob⟩ := checkedBounds_negSucc_oob_64 ⟨7, by decide⟩
    (Size.ofBytes 32) (Size.ofBytes 4) 7 .memoryAccess
    (by decide) (Or.inl (by decide))
  let ⟨raw0, h_fb0, _⟩ := miriAlloc_fromBytes_spec
    (Prov := Miri.Memory.Provenance) (Array.replicate 8 0) Align.EIGHT .Mut
    (Miri.TreeBorrows.BorrowTree.new BorTag.one (Size.ofBytes 8))
    (by decide) (by decide)
  let ⟨after, h_wp, h_rs⟩ := miriAlloc_writePointer_readScalar_roundTrip
    ptr (Miri.TreeBorrows.BorrowTree.new BorTag.one (Size.ofBytes 8)) raw0 h_fb0
  exact ⟨h_off, h_in, ⟨signedOff, h_oob⟩, ⟨signedOffNeg, h_noob⟩, raw0, after,
    h_fb0, h_wp, h_rs⟩

end Anneal.MirCorrespondence
