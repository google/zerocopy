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
public import Trusted.MirAst.Types
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Anneal.ByteSubLens.Lens
public import Anneal.AsmBridge.FlagsAndStack

public section

namespace Anneal.AsmBridge.MemoryWindow

open Trusted.MirAst Trusted.MirSemantics Anneal.ByteSubLens
open Anneal.AsmBridge.FlagsAndStack

/-!
# Exposed MIR Memory Windows, Byte-Bridge Soundness, & 2D Strided Patches

Zero-TCB (`0` `noncomputable`, `0` `._unsafe_rec`, axioms `⊆ {propext}`)
memory-window isolation and byte-level read/write bridge built directly atop
live `Trusted.MirModel` and `Trusted.MirSemantics.Memory`:

1. **Return-Address Slot & Stack-Scratch Isolation (`ExposedWindowMapWf`):**
   Checks via `List.foldr` explicit `distinctExposedAllocIds`, live MIR
   allocations, non-NULL aligned bases (`baseAddr ≠ 0`, `baseAddr < 2^w`,
   `baseAddr % 2^alignLog2 = 0`), pointer-width range bounds, pairwise
   byte-disjoint address spans, and strict disjointness from
   `protectedStackRegion spec entrySp callerFrameBytes` (protecting
   below-`SP` scratch and the caller frame / return-address slot while
   admitting both heap/`.rodata` below the stack and buffers above the caller
   frame).
2. **`AllocByte` Fail-Closed Read, Provenance-Stripping Write, & Bridge:**
   - `readExposedMachineByte`: returns `some b` only on live, in-bounds
     `AllocByte.init b _`; fails closed (`none`) on `AllocByte.uninit`, dead,
     OOB, or unmapped addresses.
   - `commitMachineByteWrites`: fails closed on unmapped, immutable `.shared`,
     dead, or OOB writes, strips provenance (`AllocByte.init b none`), and
     proves `lookupMirAlloc_updateAlloc_ne`,
     `commitMachineByteWrites_preserves_unexposed`, and
     `overlapping_unaligned_copy_ok`.
   - Bridge theorems `exposedWindow_read_implies_asmStackAccessValid` and
     `exposedWindow_write_implies_asmStackAccessValid` link
     `ExposedWindowMapWf` directly to `asmStackAccessValid = true`.
3. **Symbolic Strided 2D Window & 16-Call Macroblock Disjointness:**
   Proves `macroblock16_all_strides_ge32_disjoint` symbolically for ALL `base`,
   ALL `strideBytes >= 32`, and ALL distinct `i, j < 16`, plus
   `macroblock16_stride32_all_disjoint` and
   `macroblock16_caller_frame_preserved` with a `512`-byte macroblock buffer.
-/

/-! ## Constructive `Bool` and `Nat` Helpers -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

private theorem borTrueRight (b : Bool) : (b || true) = true := by
  cases b <;> rfl

private theorem natBeq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem le_of_natBle {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := by
  revert b
  induction a with
  | zero =>
    intro b _
    exact Nat.zero_le b
  | succ a' ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact Nat.succ_le_succ (ih h)

private theorem natBle_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by
  revert b
  induction a with
  | zero =>
    intro b _
    rfl
  | succ a' ih =>
    intro b h
    cases b with
    | zero => cases h
    | succ b' => exact ih (Nat.le_of_succ_le_succ h)

private theorem natBle_false_of_lt {a b : Nat} (h : b + 1 ≤ a) :
    Nat.ble a b = false := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases h
  | succ a' ih =>
    intro b h
    cases b with
    | zero => rfl
    | succ b' => exact ih (Nat.le_of_succ_le_succ h)

private theorem nat_trichotomy (a b : Nat) :
    a + 1 ≤ b ∨ b + 1 ≤ a ∨ a = b := by
  revert b
  induction a with
  | zero =>
    intro b
    cases b with
    | zero => exact Or.inr (Or.inr rfl)
    | succ b' => exact Or.inl (Nat.succ_le_succ (Nat.zero_le b'))
  | succ a' ih =>
    intro b
    cases b with
    | zero => exact Or.inr (Or.inl (Nat.succ_le_succ (Nat.zero_le a')))
    | succ b' =>
      cases ih b' with
      | inl h => exact Or.inl (Nat.succ_le_succ h)
      | inr h =>
        cases h with
        | inl h2 => exact Or.inr (Or.inl (Nat.succ_le_succ h2))
        | inr hEq => exact Or.inr (Or.inr (congrArg Nat.succ hEq))

private theorem nat_add_sub_cancel_le {a b : Nat} (h : a ≤ b) :
    a + (b - a) = b := by
  revert b
  induction a with
  | zero =>
    intro b _
    exact Nat.zero_add b
  | succ a' ih =>
    intro b h
    cases b with
    | zero => cases h
    | succ b' =>
      have hSub : Nat.succ b' - Nat.succ a' = b' - a' := Nat.succ_sub_succ b' a'
      rw [hSub, Nat.succ_add]
      exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

/-! ## Section 1: Exposed Window Map & Return-Address Slot Isolation -/

/-- Alias for `protectedStackRegion` protecting below-`SP` scratch and the
caller frame / return-address slot. -/
@[expose] def protectedStackAndRetWindow (spec : AsmStackSpec)
    (entrySp retSlotBytes : Nat) : ByteInterval :=
  protectedStackRegion spec entrySp retSlotBytes

/-- Membership check for `allocId` in an `ExposedMirAlloc` list (`List.foldr`,
`0` `._unsafe_rec`). -/
@[expose] def allocIdInExposedMap (id : AllocId)
    (map : List ExposedMirAlloc) : Bool :=
  map.foldr (fun exp acc => Nat.beq exp.allocId id || acc) false

/-- Explicit duplicate-free `allocId` invariant on `map` (`List.foldr`, `0`
`._unsafe_rec`). -/
@[expose] def distinctExposedAllocIds (map : List ExposedMirAlloc) : Bool :=
  (map.foldr
    (fun exp st =>
      (!allocIdInExposedMap exp.allocId st.2 && st.1, exp :: st.2))
    (true, [])).1

/-- Resolve an `ExposedMirAlloc` entry to its live `ByteInterval`
`[baseAddr, baseAddr + a.bytes.length)` in `m`. -/
@[expose] def exposedAllocInterval (m : MemoryState)
    (exp : ExposedMirAlloc) : Option ByteInterval :=
  match lookupMirAlloc exp.allocId m with
  | none => none
  | some a =>
    if a.live then some ⟨exp.baseAddr, a.bytes.length⟩ else none

/-- Check via `List.foldr` that placement `(id, iv)` is distinct in `allocId`
and byte-disjoint from every entry in `seen` (`0` `._unsafe_rec`). -/
@[expose] def exposedDisjointFromSeen (id : AllocId) (iv : ByteInterval)
    (seen : List (AllocId × ByteInterval)) : Bool :=
  seen.foldr
    (fun s acc =>
      !Nat.beq id s.1 && byteIntervalsDisjoint iv s.2 && acc)
    true

/-- Check that an exposed allocation base address `baseAddr` is non-NULL,
strictly below `2^spec.pointerBits`, and aligned to `2^alignLog2` (requiring
`alignLog2 < spec.pointerBits`). -/
@[expose] def exposedBaseValid (spec : AsmStackSpec)
    (baseAddr alignLog2 : Nat) : Bool :=
  !Nat.beq baseAddr 0 &&
  Nat.blt baseAddr (maxAddrBound spec) &&
  Nat.blt alignLog2 spec.pointerBits &&
  Nat.beq (Nat.mod baseAddr (Nat.pow 2 alignLog2)) 0

/-- Entry-level liveness, non-NULL/alignment/pointer-width validity,
protected-window disjointness, and pairwise disjointness check (`List.foldr`,
`0` `._unsafe_rec`). -/
@[expose] def exposedEntriesWf (m : MemoryState) (spec : AsmStackSpec)
    (protWin : ByteInterval) (map : List ExposedMirAlloc) : Bool :=
  (map.foldr
    (fun exp st =>
      match lookupMirAlloc exp.allocId m with
      | none => (false, st.2)
      | some a =>
        if !a.live then
          (false, st.2)
        else
          let iv : ByteInterval := ⟨exp.baseAddr, a.bytes.length⟩
          let baseOk := exposedBaseValid spec exp.baseAddr a.alignLog2
          let ptrOk := addrRangeFitsPointerBits spec iv.start iv.len
          let protOk := byteIntervalsDisjoint iv protWin
          let disjOk := exposedDisjointFromSeen exp.allocId iv st.2
          (baseOk && ptrOk && protOk && disjOk && st.1,
            (exp.allocId, iv) :: st.2))
    (true, [])).1

/-- Well-formedness check for an exposed MIR allocation map (`List.foldr`,
`0` `._unsafe_rec`):
1. `stackRegionFitsPointerBits spec entrySp retSlotBytes = true` (strict
   non-NULL headroom `spec.stackHeadroomBytes < entrySp` and strict
   non-wraparound `entrySp + retSlotBytes < 2^spec.pointerBits`).
2. `distinctExposedAllocIds map = true` (explicit unique allocation IDs).
3. Every `(allocId, baseAddr)` maps a live MIR allocation `a` in `m` with
   non-NULL `baseAddr ≠ 0`, strict base bound `baseAddr < 2^spec.pointerBits`,
   alignment `a.alignLog2 < spec.pointerBits` and
   `baseAddr % 2^a.alignLog2 = 0`, and strict non-wraparound end bound
   `baseAddr + len < 2^spec.pointerBits` (`addrRangeFitsPointerBits`, so the
   one-past-the-end pointer never wraps to `0`).
4. Every exposed allocation is strictly byte-disjoint from
   `[entrySp - spec.stackHeadroomBytes, entrySp + retSlotBytes)` (protecting
   below-`SP` scratch and the caller's return-address slot / caller frame; as a
   fail-closed coverage boundary, Rust stack buffers located inside the
   caller-frame span `[entrySp, entrySp + retSlotBytes)` cannot be exposed into
   `asm!` without per-slot frame splitting, while heap/`.rodata` below the stack
   and buffers above the protected caller frame are admitted).
5. All exposed entries are pairwise byte-disjoint in address space. -/
@[expose] def ExposedWindowMapWf (m : MemoryState) (spec : AsmStackSpec)
    (entrySp retSlotBytes : Nat) (map : List ExposedMirAlloc) : Bool :=
  stackRegionFitsPointerBits spec entrySp retSlotBytes &&
  distinctExposedAllocIds map &&
  exposedEntriesWf m spec (protectedStackRegion spec entrySp retSlotBytes) map

/-- Concrete rejection when an exposed buffer overlaps the caller's
return-address slot `[entrySp, entrySp + 8)`, below-`SP` scratch, or another
exposed allocation, vs admission when placed cleanly on the heap below the
stack or above `[entrySp, entrySp + 8)` (`[]` axioms). -/
theorem exposedWindow_rejects_return_addr_overlap :
    let spec := sysvX64StackSpec 4096
    let entrySp : Nat := 65536
    let bufBytes : List AllocByte :=
      [.init 1, .init 2, .init 3, .init 4,
       .init 5, .init 6, .init 7, .init 8]
    let mem : MemoryState :=
      { nextAllocId := 3
        allocations :=
          [{ allocId := 1, alignLog2 := 3, mutability := .mut,
             bytes := bufBytes, live := true },
           { allocId := 2, alignLog2 := 3, mutability := .mut,
             bytes := bufBytes, live := true }] }
    let mapRetOverlap : List ExposedMirAlloc := [⟨1, entrySp + 4⟩]
    let mapScratchOverlap : List ExposedMirAlloc := [⟨1, entrySp - 16⟩]
    let mapSelfOverlap : List ExposedMirAlloc :=
      [⟨1, entrySp + 16⟩, ⟨2, entrySp + 20⟩]
    let mapDupId : List ExposedMirAlloc :=
      [⟨1, entrySp + 8⟩, ⟨1, entrySp + 32⟩]
    let mapCleanHeapAndFrame : List ExposedMirAlloc :=
      [⟨1, entrySp + 8⟩, ⟨2, 16384⟩]
    ExposedWindowMapWf mem spec entrySp 8 mapRetOverlap = false ∧
    ExposedWindowMapWf mem spec entrySp 8 mapScratchOverlap = false ∧
    ExposedWindowMapWf mem spec entrySp 8 mapSelfOverlap = false ∧
    ExposedWindowMapWf mem spec entrySp 8 mapDupId = false ∧
    ExposedWindowMapWf mem spec entrySp 8 mapCleanHeapAndFrame = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 2: `AllocByte` Fail-Closed Read & Provenance-Stripping Write -/

/-- Total `List.foldr` byte lookup (`0` `._unsafe_rec`). -/
@[expose] def getAllocByteAt (bs : List AllocByte) (idx : Nat) :
    Option AllocByte :=
  (bs.foldr
    (fun b go k =>
      match k with
      | 0 => some b
      | k' + 1 => go k')
    (fun _ => none)) idx

/-- Total `List.foldr` single-byte replacement (`0` `._unsafe_rec`). -/
@[expose] def setAllocByteAt (bs : List AllocByte) (idx : Nat)
    (v : AllocByte) : Option (List AllocByte) :=
  (bs.foldr
    (fun b (st : List AllocByte × (Nat → Option (List AllocByte))) =>
      (b :: st.1, fun k =>
        match k with
        | 0 => some (v :: st.1)
        | k' + 1 =>
          match st.2 k' with
          | none => none
          | some rest => some (b :: rest)))
    ([], fun _ => none)).2 idx

/-- Total `@Nat.rec` byte-list replication (`0` `._unsafe_rec`). -/
@[expose] def replicateAllocByte (n : Nat) (b : AllocByte) : List AllocByte :=
  @Nat.rec (fun _ => List AllocByte) [] (fun _ ih => b :: ih) n

/-- Exact length of `replicateAllocByte` without kernel recursion blowup (`[]`
axioms). -/
theorem replicateAllocByte_length (n : Nat) (b : AllocByte) :
    (replicateAllocByte n b).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change (b :: replicateAllocByte k b).length = k + 1
    dsimp only [List.length]
    rw [ih]

/-- Resolve raw machine address `addr` against `map` in `m`, returning the
covering `(Allocation, byteOffset)` iff `baseAddr <= addr < baseAddr + len`
(`List.foldr`, `0` `._unsafe_rec`). -/
@[expose] def resolveAddrInMap (m : MemoryState)
    (map : List ExposedMirAlloc) (addr : Nat) : Option (Allocation × Nat) :=
  map.foldr
    (fun exp acc =>
      match lookupMirAlloc exp.allocId m with
      | none => acc
      | some a =>
        if Nat.ble exp.baseAddr addr &&
           Nat.blt (addr - exp.baseAddr) a.bytes.length then
          some (a, addr - exp.baseAddr)
        else
          acc)
    none

/-- Fail-closed machine byte read from exposed MIR memory: returns `some b`
only when `addr` resolves to a live allocation in-bounds at
`AllocByte.init b _`, returning `none` (UB) on `AllocByte.uninit`, dead, OOB,
or unmapped addresses. -/
@[expose] def readExposedMachineByte (m : MemoryState)
    (map : List ExposedMirAlloc) (addr : Nat) : Option UInt8 :=
  match resolveAddrInMap m map addr with
  | none => none
  | some (a, off) =>
    if !a.live then
      none
    else
      match getAllocByteAt a.bytes off with
      | some (.init b _) => some b
      | some .uninit | none => none

/-- Resolve raw machine span `[addr, addr + len)` against `map` in `m`,
returning the covering live `(Allocation, byteOffset)` iff `a.live`,
`baseAddr <= addr`, and `(addr - baseAddr) + len <= a.bytes.length`
(`List.foldr`, `0` `._unsafe_rec`), matching `resolveExposedMirAccess` for
both `len = 0` and `len > 0`. -/
@[expose] def resolveSpanInMap (m : MemoryState)
    (map : List ExposedMirAlloc) (addr len : Nat) :
    Option (Allocation × Nat) :=
  map.foldr
    (fun exp acc =>
      match lookupMirAlloc exp.allocId m with
      | none => acc
      | some a =>
        if a.live &&
           Nat.ble exp.baseAddr addr &&
           Nat.ble (addr - exp.baseAddr + len) a.bytes.length then
          some (a, addr - exp.baseAddr)
        else
          acc)
    none

/-- Read `len` consecutive initialized bytes starting at offset `off` inside a
single allocation byte list via `@Nat.rec` (`0` `._unsafe_rec`), failing closed
on `.uninit` or out-of-bounds offsets (including `len = 0` with
`off > bs.length`). -/
@[expose] def readInitBytesFromAlloc (bs : List AllocByte) (off len : Nat) :
    Option (List UInt8) :=
  if !Nat.ble (off + len) bs.length then
    none
  else
    (@Nat.rec (fun _ => Nat → Option (List UInt8))
      (fun _ => some [])
      (fun _ ih cur =>
        match getAllocByteAt bs cur with
        | some (.init b _) =>
          match ih (cur + 1) with
          | none => none
          | some rest => some (b :: rest)
        | some .uninit | none => none)
      len) off

/-- Sequential unaligned multi-byte read enforcing
`addrRangeFitsPointerBits spec addr len` (`addr >= 1` and
`addr + len < 2^spec.pointerBits`), resolving the span `[addr, addr + len)`
ONCE inside a single live exposed allocation (`off + len <= a.bytes.length`),
and never short-circuiting `len = 0` (matching `resolveExposedMirAccess` and
`asmStackAccessValid` for all `len`, including `len = 0`, and rejecting loads
across two adjacent allocations). -/
@[expose] def readExposedMachineBytes (spec : AsmStackSpec) (m : MemoryState)
    (map : List ExposedMirAlloc) (addr len : Nat) : Option (List UInt8) :=
  if !addrRangeFitsPointerBits spec addr len then
    none
  else
    match resolveSpanInMap m map addr len with
    | none => none
    | some (a, off) =>
      readInitBytesFromAlloc a.bytes off len

/-- Pure `List.foldr` allocation replacement in `MemoryState` (`0`
`._unsafe_rec`). -/
@[expose] def updateMirAlloc (a' : Allocation) (m : MemoryState) :
    MemoryState :=
  { m with
    allocations :=
      m.allocations.foldr
        (fun a acc =>
          if Nat.beq a.allocId a'.allocId then a' :: acc else a :: acc)
        [] }

/-- Computable mutability predicate avoiding keyword pattern issues. -/
@[expose] def isMutableAlloc : Mutability → Bool
  | .mut => true
  | .shared => false

/-- Commit a single raw machine byte write `(addr, b)` into exposed MIR memory:
- fails closed (`none`) on unmapped, OOB, dead, or `.shared` allocations;
- strips pointer provenance by writing `AllocByte.init b none`. -/
@[expose] def commitOneMachineByteWrite (m : MemoryState)
    (map : List ExposedMirAlloc) (w : Nat × UInt8) : Option MemoryState :=
  match resolveAddrInMap m map w.1 with
  | none => none
  | some (a, off) =>
    if !(a.live && isMutableAlloc a.mutability) then
      none
    else
      match setAllocByteAt a.bytes off (.init w.2 none) with
      | none => none
      | some bs' => some (updateMirAlloc { a with bytes := bs' } m)

/-- Commit a sequence of raw machine byte writes into exposed MIR memory via
`List.foldl` (`0` `._unsafe_rec`). -/
@[expose] def commitMachineByteWrites (m : MemoryState)
    (map : List ExposedMirAlloc) (writes : List (Nat × UInt8)) :
    Option MemoryState :=
  writes.foldl
    (fun st w =>
      match st with
      | none => none
      | some cur => commitOneMachineByteWrite cur map w)
    (some m)

/-- Build consecutive `(addr + i, b_i)` write events from a base address and
byte list (`List.foldr`, `0` `._unsafe_rec`). -/
@[expose] def mkByteWrites (baseAddr : Nat) (bs : List UInt8) :
    List (Nat × UInt8) :=
  (bs.foldr
    (fun b go cur => (cur, b) :: go (cur + 1))
    (fun _ => [])) baseAddr

/-! ### Frame-Preservation, Provenance-Stripping, & Stack-Bridge Theorems -/

private theorem lookupMirAlloc_list_id (id : AllocId) (xs : List Allocation)
    (a : Allocation)
    (h : xs.foldr
      (fun x acc => if Nat.beq x.allocId id then some x else acc) none =
      some a) :
    a.allocId = id := by
  induction xs with
  | nil => cases h
  | cons x rest ih =>
    dsimp only [List.foldr] at h
    cases hEq : Nat.beq x.allocId id with
    | true =>
      rw [ite_bool_true hEq] at h
      have hId := natEq_of_beq x.allocId id hEq
      cases h
      exact hId
    | false =>
      rw [ite_bool_false hEq] at h
      exact ih h

private theorem lookupMirAlloc_id (id : AllocId) (m : MemoryState)
    (a : Allocation) (h : lookupMirAlloc id m = some a) :
    a.allocId = id :=
  lookupMirAlloc_list_id id m.allocations a h

private theorem lookupMirAlloc_updateAlloc_list_ne (a' : Allocation)
    (targetId : AllocId) (hne : Nat.beq a'.allocId targetId = false)
    (xs : List Allocation) :
    (xs.foldr
      (fun a acc =>
        if Nat.beq a.allocId a'.allocId then a' :: acc else a :: acc)
      []).foldr
      (fun a acc => if Nat.beq a.allocId targetId then some a else acc)
      none =
    xs.foldr
      (fun a acc => if Nat.beq a.allocId targetId then some a else acc)
      none := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [List.foldr]
    cases hMatch : Nat.beq x.allocId a'.allocId with
    | false =>
      rw [ite_bool_false rfl]
      dsimp only [List.foldr]
      cases hTgt : Nat.beq x.allocId targetId with
      | true =>
        rw [ite_bool_true rfl, ite_bool_true rfl]
      | false =>
        rw [ite_bool_false rfl, ite_bool_false rfl]
        exact ih
    | true =>
      rw [ite_bool_true rfl]
      dsimp only [List.foldr]
      have hXeq := natEq_of_beq x.allocId a'.allocId hMatch
      have hXne : Nat.beq x.allocId targetId = false := by
        rw [hXeq]; exact hne
      rw [ite_bool_false hne, ite_bool_false hXne]
      exact ih

/-- Updating allocation `a'` preserves every MIR allocation with a distinct
`allocId` identically (`[]` axioms). -/
theorem lookupMirAlloc_updateAlloc_ne (a' : Allocation) (m : MemoryState)
    (targetId : AllocId) (hne : Nat.beq a'.allocId targetId = false) :
    lookupMirAlloc targetId (updateMirAlloc a' m) =
      lookupMirAlloc targetId m :=
  lookupMirAlloc_updateAlloc_list_ne a' targetId hne m.allocations

private theorem resolveAddrInMap_in_map (m : MemoryState)
    (map : List ExposedMirAlloc) (addr : Nat) (a : Allocation) (off : Nat)
    (h : resolveAddrInMap m map addr = some (a, off)) :
    allocIdInExposedMap a.allocId map = true := by
  induction map with
  | nil => cases h
  | cons exp rest ih =>
    dsimp only [resolveAddrInMap, List.foldr] at h
    change (Nat.beq exp.allocId a.allocId ||
      allocIdInExposedMap a.allocId rest) = true
    cases hLu : lookupMirAlloc exp.allocId m with
    | none =>
      rw [hLu] at h
      dsimp only at h
      have hTail := ih h
      rw [hTail, borTrueRight]
    | some a0 =>
      rw [hLu] at h
      dsimp only at h
      cases hIn : (Nat.ble exp.baseAddr addr &&
          Nat.blt (addr - exp.baseAddr) a0.bytes.length) with
      | true =>
        rw [ite_bool_true hIn] at h
        cases h
        have hId := lookupMirAlloc_id exp.allocId m a hLu
        rw [hId, natBeq_refl exp.allocId]
        rfl
      | false =>
        rw [ite_bool_false hIn] at h
        have hTail := ih h
        rw [hTail, borTrueRight]

private theorem commitOneMachineByteWrite_preserves_unexposed
    (m m' : MemoryState) (map : List ExposedMirAlloc) (w : Nat × UInt8)
    (targetId : AllocId)
    (hUnexp : allocIdInExposedMap targetId map = false)
    (hStep : commitOneMachineByteWrite m map w = some m') :
    lookupMirAlloc targetId m' = lookupMirAlloc targetId m := by
  unfold commitOneMachineByteWrite at hStep
  cases hRes : resolveAddrInMap m map w.1 with
  | none =>
    rw [hRes] at hStep
    cases hStep
  | some pair =>
    cases pair with
    | mk a off =>
      rw [hRes] at hStep
      dsimp only at hStep
      have hInMap := resolveAddrInMap_in_map m map w.1 a off hRes
      have hNe : Nat.beq a.allocId targetId = false := by
        cases hEq : Nat.beq a.allocId targetId with
        | false => rfl
        | true =>
          have hIdEq := natEq_of_beq a.allocId targetId hEq
          rw [hIdEq] at hInMap
          rw [hInMap] at hUnexp
          exact False.elim (boolFalseNeTrue hUnexp.symm)
      cases hPerm : (a.live && isMutableAlloc a.mutability) with
      | false =>
        rw [hPerm] at hStep
        cases hStep
      | true =>
        rw [hPerm] at hStep
        dsimp only [Bool.not] at hStep
        rw [ite_bool_false rfl] at hStep
        cases hSet : setAllocByteAt a.bytes off (.init w.2 none) with
        | none =>
          rw [hSet] at hStep
          cases hStep
        | some bs' =>
          rw [hSet] at hStep
          cases hStep
          exact lookupMirAlloc_updateAlloc_ne
            { a with bytes := bs' } m targetId hNe

private theorem foldl_commit_none (map : List ExposedMirAlloc)
    (writes : List (Nat × UInt8)) :
    writes.foldl
      (fun st w =>
        match st with
        | none => none
        | some cur => commitOneMachineByteWrite cur map w)
      none = none := by
  induction writes with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Committing any sequence of raw machine byte writes preserves every
unexposed MIR `Allocation` (bytes, `.uninit` mask, `prov` provenance,
alignment, mutability, and liveness) identically (`[]` axioms). -/
theorem commitMachineByteWrites_preserves_unexposed
    (writes : List (Nat × UInt8)) (m m' : MemoryState)
    (map : List ExposedMirAlloc) (targetId : AllocId)
    (hUnexp : allocIdInExposedMap targetId map = false)
    (hCommit : commitMachineByteWrites m map writes = some m') :
    lookupMirAlloc targetId m' = lookupMirAlloc targetId m := by
  unfold commitMachineByteWrites at hCommit
  induction writes generalizing m with
  | nil =>
    cases hCommit
    rfl
  | cons w rest ih =>
    dsimp only [List.foldl] at hCommit
    cases hOne : commitOneMachineByteWrite m map w with
    | none =>
      rw [hOne, foldl_commit_none] at hCommit
      cases hCommit
    | some m1 =>
      rw [hOne] at hCommit
      have hRest := ih m1 hCommit
      have hFirst :=
        commitOneMachineByteWrite_preserves_unexposed m m1 map w targetId
          hUnexp hOne
      rw [hRest, hFirst]

private theorem exposedEntriesWf_resolve_bridge (m : MemoryState)
    (spec : AsmStackSpec) (protWin : ByteInterval) (map : List ExposedMirAlloc)
    (addr : Nat) (a : Allocation) (off : Nat) (isWrite : Bool)
    (hWf : exposedEntriesWf m spec protWin map = true)
    (hRes : resolveAddrInMap m map addr = some (a, off))
    (hMut : isWrite = false ∨ isMutableAlloc a.mutability = true) :
    (∃ baseAddr,
      Nat.ble baseAddr addr = true ∧
      Nat.blt (addr - baseAddr) a.bytes.length = true ∧
      exposedBaseValid spec baseAddr a.alignLog2 = true ∧
      addrRangeFitsPointerBits spec baseAddr a.bytes.length = true ∧
      byteIntervalsDisjoint ⟨baseAddr, a.bytes.length⟩ protWin = true) ∧
    resolveExposedMirAccess m map addr 1 isWrite = true := by
  induction map with
  | nil => cases hRes
  | cons exp rest ih =>
    dsimp only [exposedEntriesWf, List.foldr] at hWf
    dsimp only [resolveAddrInMap, List.foldr] at hRes
    cases hLu : lookupMirAlloc exp.allocId m with
    | none =>
      rw [hLu] at hWf
      dsimp only at hWf
      exact False.elim (boolFalseNeTrue hWf)
    | some a0 =>
      rw [hLu] at hWf
      dsimp only at hWf
      cases hLive0 : a0.live with
      | false =>
        rw [hLive0] at hWf
        dsimp only [Bool.not] at hWf
        rw [ite_bool_true rfl] at hWf
        dsimp only at hWf
        exact False.elim (boolFalseNeTrue hWf)
      | true =>
        rw [hLive0] at hWf
        dsimp only [Bool.not] at hWf
        rw [ite_bool_false rfl] at hWf
        dsimp only at hWf
        have hBaseOk0 := bandLeft (bandLeft (bandLeft (bandLeft hWf)))
        have hPtr0 := bandRight (bandLeft (bandLeft (bandLeft hWf)))
        have hProt0 := bandRight (bandLeft (bandLeft hWf))
        have hWfRest : exposedEntriesWf m spec protWin rest = true :=
          bandRight hWf
        rw [hLu] at hRes
        dsimp only at hRes
        cases hIn : (Nat.ble exp.baseAddr addr &&
            Nat.blt (addr - exp.baseAddr) a0.bytes.length) with
        | true =>
          rw [ite_bool_true hIn] at hRes
          cases hRes
          have hBase := bandLeft hIn
          have hLen := bandRight hIn
          have hAddrPos : Nat.blt 0 addr = true :=
            natBle_of_le (Nat.le_trans (le_of_natBle (bandLeft hPtr0))
              (le_of_natBle hBase))
          refine ⟨⟨exp.baseAddr, hBase, hLen, hBaseOk0, hPtr0, hProt0⟩, ?_⟩
          unfold resolveExposedMirAccess
          dsimp only [List.foldr]
          have hPerm :
              mirMemPermitsAccess m exp.allocId (addr - exp.baseAddr) 1
                isWrite = true := by
            unfold mirMemPermitsAccess
            rw [hLu]
            dsimp only
            rw [hLive0]
            cases isWrite with
            | false => exact hLen
            | true =>
              cases hMut with
              | inl hFalse => exact False.elim (boolFalseNeTrue hFalse.symm)
              | inr hM =>
                change (true && isMutableAlloc a.mutability &&
                  Nat.ble (addr - exp.baseAddr + 1) a.bytes.length) = true
                rw [hM]
                exact hLen
          rw [hAddrPos, hBase, hPerm]
          rfl
        | false =>
          rw [ite_bool_false hIn] at hRes
          have hRec := ih hWfRest hRes
          refine ⟨hRec.1, ?_⟩
          have hTailRes := hRec.2
          unfold resolveExposedMirAccess at hTailRes
          unfold resolveExposedMirAccess
          dsimp only [List.foldr]
          rw [bandLeft hTailRes, bandRight hTailRes, borTrueRight]
          rfl

private theorem exposedEntriesWf_resolveSpan_bridge (m : MemoryState)
    (spec : AsmStackSpec) (protWin : ByteInterval) (map : List ExposedMirAlloc)
    (addr len : Nat) (a : Allocation) (off : Nat)
    (hWf : exposedEntriesWf m spec protWin map = true)
    (hRes : resolveSpanInMap m map addr len = some (a, off)) :
    (∃ baseAddr,
      Nat.ble baseAddr addr = true ∧
      Nat.ble (addr - baseAddr + len) a.bytes.length = true ∧
      exposedBaseValid spec baseAddr a.alignLog2 = true ∧
      addrRangeFitsPointerBits spec baseAddr a.bytes.length = true ∧
      byteIntervalsDisjoint ⟨baseAddr, a.bytes.length⟩ protWin = true) ∧
    resolveExposedMirAccess m map addr len false = true := by
  induction map with
  | nil => cases hRes
  | cons exp rest ih =>
    dsimp only [exposedEntriesWf, List.foldr] at hWf
    dsimp only [resolveSpanInMap, List.foldr] at hRes
    cases hLu : lookupMirAlloc exp.allocId m with
    | none =>
      rw [hLu] at hWf
      dsimp only at hWf
      exact False.elim (boolFalseNeTrue hWf)
    | some a0 =>
      rw [hLu] at hWf
      dsimp only at hWf
      cases hLive0 : a0.live with
      | false =>
        rw [hLive0] at hWf
        dsimp only [Bool.not] at hWf
        rw [ite_bool_true rfl] at hWf
        dsimp only at hWf
        exact False.elim (boolFalseNeTrue hWf)
      | true =>
        rw [hLive0] at hWf
        dsimp only [Bool.not] at hWf
        rw [ite_bool_false rfl] at hWf
        dsimp only at hWf
        have hBaseOk0 := bandLeft (bandLeft (bandLeft (bandLeft hWf)))
        have hPtr0 := bandRight (bandLeft (bandLeft (bandLeft hWf)))
        have hProt0 := bandRight (bandLeft (bandLeft hWf))
        have hWfRest : exposedEntriesWf m spec protWin rest = true :=
          bandRight hWf
        rw [hLu] at hRes
        dsimp only at hRes
        rw [hLive0, Bool.true_and] at hRes
        cases hIn : (Nat.ble exp.baseAddr addr &&
            Nat.ble (addr - exp.baseAddr + len) a0.bytes.length) with
        | true =>
          rw [ite_bool_true hIn] at hRes
          cases hRes
          have hBase := bandLeft hIn
          have hLen := bandRight hIn
          have hAddrPos : Nat.blt 0 addr = true :=
            natBle_of_le (Nat.le_trans (le_of_natBle (bandLeft hPtr0))
              (le_of_natBle hBase))
          refine ⟨⟨exp.baseAddr, hBase, hLen, hBaseOk0, hPtr0, hProt0⟩, ?_⟩
          unfold resolveExposedMirAccess
          dsimp only [List.foldr]
          have hPerm :
              mirMemPermitsAccess m exp.allocId (addr - exp.baseAddr) len
                false = true := by
            unfold mirMemPermitsAccess
            rw [hLu]
            dsimp only
            rw [hLive0]
            exact hLen
          rw [hAddrPos, hBase, hPerm]
          rfl
        | false =>
          rw [ite_bool_false hIn] at hRes
          have hRec := ih hWfRest hRes
          refine ⟨hRec.1, ?_⟩
          have hTailRes := hRec.2
          unfold resolveExposedMirAccess at hTailRes
          unfold resolveExposedMirAccess
          dsimp only [List.foldr]
          rw [bandLeft hTailRes, bandRight hTailRes, borTrueRight]
          rfl

private theorem subinterval_len_disjoint
    (spec : AsmStackSpec) (entrySp callerFrameBytes baseAddr allocLen
      addr len : Nat)
    (hBase : Nat.ble baseAddr addr = true)
    (hIn : Nat.ble (addr - baseAddr + len) allocLen = true)
    (hPtr : addrRangeFitsPointerBits spec baseAddr allocLen = true)
    (hDisj : byteIntervalsDisjoint ⟨baseAddr, allocLen⟩
      (protectedStackRegion spec entrySp callerFrameBytes) = true) :
    addrRangeFitsPointerBits spec addr len = true ∧
    byteIntervalsDisjoint ⟨addr, len⟩
      (protectedStackRegion spec entrySp callerFrameBytes) = true := by
  have hBaseLe : baseAddr ≤ addr := le_of_natBle hBase
  have hSpanLe : addr - baseAddr + len ≤ allocLen := le_of_natBle hIn
  have hAddrEnd : addr + len ≤ baseAddr + allocLen := by
    have h1 := Nat.add_le_add_left hSpanLe baseAddr
    rw [← Nat.add_assoc, nat_add_sub_cancel_le hBaseLe] at h1
    exact h1
  have hBasePos : 1 ≤ baseAddr := le_of_natBle (bandLeft hPtr)
  have hEndLt : baseAddr + allocLen + 1 ≤ maxAddrBound spec :=
    le_of_natBle (bandRight hPtr)
  have hPtrFits : addrRangeFitsPointerBits spec addr len = true := by
    unfold addrRangeFitsPointerBits Nat.blt
    rw [natBle_of_le (Nat.le_trans hBasePos hBaseLe),
        natBle_of_le (Nat.le_trans (Nat.succ_le_succ hAddrEnd) hEndLt)]
    rfl
  refine ⟨hPtrFits, ?_⟩
  unfold byteIntervalsDisjoint rangesDisjoint protectedStackRegion at hDisj
  unfold byteIntervalsDisjoint rangesDisjoint protectedStackRegion
  dsimp only at hDisj
  dsimp only
  cases hLeft :
      Nat.ble (baseAddr + allocLen) (entrySp - spec.stackHeadroomBytes) with
  | true =>
    have hLeftLe : baseAddr + allocLen ≤ entrySp - spec.stackHeadroomBytes :=
      le_of_natBle hLeft
    have hAEndLe : addr + len ≤ entrySp - spec.stackHeadroomBytes :=
      Nat.le_trans hAddrEnd hLeftLe
    rw [natBle_of_le hAEndLe]
    rfl
  | false =>
    rw [hLeft] at hDisj
    dsimp only [Bool.or] at hDisj
    have hRightLe :
        (entrySp - spec.stackHeadroomBytes) +
          (spec.stackHeadroomBytes + callerFrameBytes) ≤ baseAddr :=
      le_of_natBle hDisj
    have hRightAddr :
        (entrySp - spec.stackHeadroomBytes) +
          (spec.stackHeadroomBytes + callerFrameBytes) ≤ addr :=
      Nat.le_trans hRightLe hBaseLe
    rw [natBle_of_le hRightAddr, borTrueRight]

private theorem subinterval_disjoint_and_outside_scratch
    (spec : AsmStackSpec) (entrySp callerFrameBytes baseAddr len addr : Nat)
    (hHead : Nat.blt spec.stackHeadroomBytes entrySp = true)
    (hBase : Nat.ble baseAddr addr = true)
    (hIn : Nat.blt (addr - baseAddr) len = true)
    (hPtr : addrRangeFitsPointerBits spec baseAddr len = true)
    (hDisj : byteIntervalsDisjoint ⟨baseAddr, len⟩
      (protectedStackRegion spec entrySp callerFrameBytes) = true) :
    addrRangeFitsPointerBits spec addr 1 = true ∧
    (Nat.ble (entrySp - spec.stackHeadroomBytes) addr &&
      Nat.ble (addr + 1) entrySp) = false ∧
    byteIntervalsDisjoint ⟨addr, 1⟩
      (protectedStackRegion spec entrySp callerFrameBytes) = true := by
  have hHeadLe : spec.stackHeadroomBytes ≤ entrySp :=
    Nat.le_trans (Nat.le_succ _) (le_of_natBle hHead)
  have hBaseLe : baseAddr ≤ addr := le_of_natBle hBase
  have hOffLt : addr - baseAddr + 1 ≤ len := le_of_natBle hIn
  have hAddrEnd : addr + 1 ≤ baseAddr + len := by
    have h1 := Nat.add_le_add_left hOffLt baseAddr
    rw [← Nat.add_assoc, nat_add_sub_cancel_le hBaseLe] at h1
    exact h1
  have hBasePos : 1 ≤ baseAddr := le_of_natBle (bandLeft hPtr)
  have hEndLt : baseAddr + len + 1 ≤ maxAddrBound spec :=
    le_of_natBle (bandRight hPtr)
  have hPtrFits : addrRangeFitsPointerBits spec addr 1 = true := by
    unfold addrRangeFitsPointerBits Nat.blt
    rw [natBle_of_le (Nat.le_trans hBasePos hBaseLe),
        natBle_of_le (Nat.le_trans (Nat.succ_le_succ hAddrEnd) hEndLt)]
    rfl
  refine ⟨hPtrFits, ?_⟩
  unfold byteIntervalsDisjoint rangesDisjoint protectedStackRegion at hDisj
  unfold byteIntervalsDisjoint rangesDisjoint protectedStackRegion
  dsimp only at hDisj
  dsimp only
  cases hLeft :
      Nat.ble (baseAddr + len) (entrySp - spec.stackHeadroomBytes) with
  | true =>
    have hLeftLe : baseAddr + len ≤ entrySp - spec.stackHeadroomBytes :=
      le_of_natBle hLeft
    have hAEndLe : addr + 1 ≤ entrySp - spec.stackHeadroomBytes :=
      Nat.le_trans hAddrEnd hLeftLe
    have hNotIn : Nat.ble (entrySp - spec.stackHeadroomBytes) addr = false :=
      natBle_false_of_lt hAEndLe
    rw [hNotIn, natBle_of_le hAEndLe]
    exact ⟨rfl, rfl⟩
  | false =>
    rw [hLeft] at hDisj
    dsimp only [Bool.or] at hDisj
    have hRightLe :
        (entrySp - spec.stackHeadroomBytes) +
          (spec.stackHeadroomBytes + callerFrameBytes) ≤ baseAddr :=
      le_of_natBle hDisj
    have hRightAddr :
        (entrySp - spec.stackHeadroomBytes) +
          (spec.stackHeadroomBytes + callerFrameBytes) ≤ addr :=
      Nat.le_trans hRightLe hBaseLe
    have hSpLeAddr : entrySp ≤ addr := by
      have hSum :
          (entrySp - spec.stackHeadroomBytes) + spec.stackHeadroomBytes =
            entrySp := by
        rw [Nat.add_comm]
        exact nat_add_sub_cancel_le hHeadLe
      have h1 :
          entrySp ≤ (entrySp - spec.stackHeadroomBytes) +
            (spec.stackHeadroomBytes + callerFrameBytes) := by
        rw [← Nat.add_assoc, hSum]
        exact Nat.le_add_right entrySp callerFrameBytes
      exact Nat.le_trans h1 hRightAddr
    have hNotEnd : Nat.ble (addr + 1) entrySp = false :=
      natBle_false_of_lt (Nat.succ_le_succ hSpLeAddr)
    have hDisjR :
        Nat.ble ((entrySp - spec.stackHeadroomBytes) +
          (spec.stackHeadroomBytes + callerFrameBytes)) addr = true :=
      natBle_of_le hRightAddr
    rw [hNotEnd, hDisjR, borTrueRight]
    cases Nat.ble (entrySp - spec.stackHeadroomBytes) addr <;> exact ⟨rfl, rfl⟩

/-- Bridge theorem linking `ExposedWindowMapWf` and a valid exposed byte read
directly to `asmStackAccessValid = true` (unifying `MemoryWindow` and
`FlagsAndStack` for both heap/`.rodata` below the stack and buffers above the
caller frame, `[]` axioms). -/
theorem exposedWindow_read_implies_asmStackAccessValid
    (m : MemoryState) (spec : AsmStackSpec) (opts : InlineAsmOptions)
    (entrySp curSp callerFrameBytes addr : Nat) (b : UInt8)
    (map : List ExposedMirAlloc)
    (hWf : ExposedWindowMapWf m spec entrySp callerFrameBytes map = true)
    (hOpts : validInlineAsmOptions opts = true)
    (hNomem : opts.nomem = false)
    (hCurLo : Nat.ble (entrySp - spec.stackHeadroomBytes) curSp = true)
    (hCurHi : Nat.ble curSp entrySp = true)
    (hRead : readExposedMachineByte m map addr = some b) :
    asmStackAccessValid spec opts m entrySp curSp callerFrameBytes map
      ⟨addr, 1, .read⟩ = true := by
  have hRegFit := bandLeft (bandLeft hWf)
  have hHead := bandLeft hRegFit
  have hEntWf := bandRight hWf
  unfold readExposedMachineByte at hRead
  cases hRes : resolveAddrInMap m map addr with
  | none =>
    rw [hRes] at hRead
    cases hRead
  | some pair =>
    cases pair with
    | mk a off =>
      have hBr := exposedEntriesWf_resolve_bridge m spec
        (protectedStackRegion spec entrySp callerFrameBytes) map addr a off
        false hEntWf hRes (Or.inl rfl)
      cases hBr.1 with
      | intro baseAddr hBaseInfo =>
        have hSub := subinterval_disjoint_and_outside_scratch spec entrySp
          callerFrameBytes baseAddr a.bytes.length addr hHead hBaseInfo.1
          hBaseInfo.2.1 hBaseInfo.2.2.2.1 hBaseInfo.2.2.2.2
        unfold asmStackAccessValid
        dsimp only
        rw [hOpts, hRegFit, hSub.1, hCurLo, hCurHi, hNomem, hSub.2.2]
        cases opts.readonly <;> exact hBr.2

/-- Multi-byte bridge theorem linking `ExposedWindowMapWf` and any valid
`readExposedMachineBytes` (for ALL `len : Nat`, including `len = 0` and
multi-byte loads) directly to `asmStackAccessValid = true` (`[]` axioms). -/
theorem exposedWindow_readBytes_implies_asmStackAccessValid
    (m : MemoryState) (spec : AsmStackSpec) (opts : InlineAsmOptions)
    (entrySp curSp callerFrameBytes addr len : Nat) (bs : List UInt8)
    (map : List ExposedMirAlloc)
    (hWf : ExposedWindowMapWf m spec entrySp callerFrameBytes map = true)
    (hOpts : validInlineAsmOptions opts = true)
    (hNomem : opts.nomem = false)
    (hCurLo : Nat.ble (entrySp - spec.stackHeadroomBytes) curSp = true)
    (hCurHi : Nat.ble curSp entrySp = true)
    (hRead : readExposedMachineBytes spec m map addr len = some bs) :
    asmStackAccessValid spec opts m entrySp curSp callerFrameBytes map
      ⟨addr, len, .read⟩ = true := by
  have hRegFit := bandLeft (bandLeft hWf)
  have hEntWf := bandRight hWf
  unfold readExposedMachineBytes at hRead
  cases hBounds : addrRangeFitsPointerBits spec addr len with
  | false =>
    rw [hBounds] at hRead
    dsimp only [Bool.not] at hRead
    rw [ite_bool_true rfl] at hRead
    cases hRead
  | true =>
    rw [hBounds] at hRead
    dsimp only [Bool.not] at hRead
    rw [ite_bool_false rfl] at hRead
    cases hRes : resolveSpanInMap m map addr len with
    | none =>
      rw [hRes] at hRead
      cases hRead
    | some pair =>
      cases pair with
      | mk a off =>
        have hBr := exposedEntriesWf_resolveSpan_bridge m spec
          (protectedStackRegion spec entrySp callerFrameBytes) map addr len
          a off hEntWf hRes
        cases hBr.1 with
        | intro baseAddr hBaseInfo =>
          have hSub := subinterval_len_disjoint spec entrySp callerFrameBytes
            baseAddr a.bytes.length addr len hBaseInfo.1 hBaseInfo.2.1
            hBaseInfo.2.2.2.1 hBaseInfo.2.2.2.2
          unfold asmStackAccessValid
          dsimp only
          rw [hOpts, hRegFit, hSub.1, hCurLo, hCurHi, hNomem, hSub.2]
          cases opts.readonly <;> exact hBr.2

/-- Bridge theorem linking `ExposedWindowMapWf` and a valid exposed byte write
directly to `asmStackAccessValid = true` (`[]` axioms). -/
theorem exposedWindow_write_implies_asmStackAccessValid
    (m m' : MemoryState) (spec : AsmStackSpec) (opts : InlineAsmOptions)
    (entrySp curSp callerFrameBytes addr : Nat) (b : UInt8)
    (map : List ExposedMirAlloc)
    (hWf : ExposedWindowMapWf m spec entrySp callerFrameBytes map = true)
    (hOpts : validInlineAsmOptions opts = true)
    (hNomem : opts.nomem = false)
    (hRo : opts.readonly = false)
    (hCurLo : Nat.ble (entrySp - spec.stackHeadroomBytes) curSp = true)
    (hCurHi : Nat.ble curSp entrySp = true)
    (hWrite : commitOneMachineByteWrite m map (addr, b) = some m') :
    asmStackAccessValid spec opts m entrySp curSp callerFrameBytes map
      ⟨addr, 1, .write⟩ = true := by
  have hRegFit := bandLeft (bandLeft hWf)
  have hHead := bandLeft hRegFit
  have hEntWf := bandRight hWf
  unfold commitOneMachineByteWrite at hWrite
  cases hRes : resolveAddrInMap m map addr with
  | none =>
    rw [hRes] at hWrite
    cases hWrite
  | some pair =>
    cases pair with
    | mk a off =>
      rw [hRes] at hWrite
      dsimp only at hWrite
      cases hPerm : (a.live && isMutableAlloc a.mutability) with
      | false =>
        rw [hPerm] at hWrite
        cases hWrite
      | true =>
        have hMut := bandRight hPerm
        have hBr := exposedEntriesWf_resolve_bridge m spec
          (protectedStackRegion spec entrySp callerFrameBytes) map addr a off
          true hEntWf hRes (Or.inr hMut)
        cases hBr.1 with
        | intro baseAddr hBaseInfo =>
          have hSub := subinterval_disjoint_and_outside_scratch spec entrySp
            callerFrameBytes baseAddr a.bytes.length addr hHead hBaseInfo.1
            hBaseInfo.2.1 hBaseInfo.2.2.2.1 hBaseInfo.2.2.2.2
          unfold asmStackAccessValid
          dsimp only
          rw [hOpts, hRegFit, hSub.1, hCurLo, hCurHi, hNomem, hRo, hSub.2.2]
          exact hBr.2

/-- Any address resolved under a well-formed exposed window map is strictly
non-NULL (`[]` axioms). -/
theorem exposedWindow_resolved_addr_ne_zero
    (m : MemoryState) (spec : AsmStackSpec)
    (entrySp callerFrameBytes addr : Nat) (a : Allocation) (off : Nat)
    (map : List ExposedMirAlloc)
    (hWf : ExposedWindowMapWf m spec entrySp callerFrameBytes map = true)
    (hRes : resolveAddrInMap m map addr = some (a, off)) :
    addr ≠ 0 := by
  have hEntWf := bandRight hWf
  have hBr := exposedEntriesWf_resolve_bridge m spec
    (protectedStackRegion spec entrySp callerFrameBytes) map addr a off
    false hEntWf hRes (Or.inl rfl)
  cases hBr.1 with
  | intro baseAddr hInfo =>
    have hBaseLe : baseAddr ≤ addr := le_of_natBle hInfo.1
    have hBaseOk := hInfo.2.2.1
    unfold exposedBaseValid at hBaseOk
    have hNonZero : (!Nat.beq baseAddr 0) = true :=
      bandLeft (bandLeft (bandLeft hBaseOk))
    intro hZero
    rw [hZero] at hBaseLe
    cases baseAddr with
    | zero => exact boolFalseNeTrue hNonZero
    | succ _ => cases hBaseLe

/-- Sequential unaligned multi-byte reads followed by overlapping unaligned
writes within the same `.mut` initialized allocation succeed cleanly (modeling
LZ77 RLE copy fastloops and in-place IDCT), stripping pointer provenance on
overwritten bytes while preserving unexposed allocations identically
(`[propext]`). -/
theorem overlapping_unaligned_copy_ok :
    let base : Nat := 0x20000
    let mem : MemoryState :=
      { nextAllocId := 3
        allocations :=
          [{ allocId := 1, alignLog2 := 4, mutability := .mut,
             bytes := [.init 0x10 none, .init 0x11 none, .init 0x22 none,
                       .init 0x33 (some 9), .init 0x44 none, .init 0x55 none,
                       .init 0x66 none, .init 0x77 none],
             live := true },
           { allocId := 2, alignLog2 := 3, mutability := .mut,
             bytes := [.uninit, .init 0xAA (some 7)],
             live := true }] }
    let map : List ExposedMirAlloc := [⟨1, base⟩]
    let srcBytes :=
      readExposedMachineBytes (sysvX64StackSpec 4096) mem map (base + 1) 4
    let writes := mkByteWrites (base + 3) [0x11, 0x22, 0x33, 0x44]
    let memAfter := commitMachineByteWrites mem map writes
    srcBytes = some [0x11, 0x22, 0x33, 0x44] ∧
    (match memAfter with
     | none => false
     | some m' =>
       match lookupMirAlloc 1 m', lookupMirAlloc 2 m' with
       | some a1, some a2 =>
         match getAllocByteAt a1.bytes 3, getAllocByteAt a1.bytes 6,
               getAllocByteAt a2.bytes 0, getAllocByteAt a2.bytes 1 with
         | some (.init b3 none), some (.init b6 none),
           some .uninit, some (.init b2 (some p2)) =>
           Nat.beq b3.toNat 0x11 && Nat.beq b6.toNat 0x44 &&
           Nat.beq b2.toNat 0xAA && Nat.beq p2 7
         | _, _, _, _ => false
       | _, _ => false) = true :=
  ⟨rfl, rfl⟩

/-! ## Section 3: Strided 2D Window & Symbolic 16-Call Macroblock Disjointness
-/

/-- Strided 2D rectangular byte patch (`rows` rows of `rowWidthBytes` bytes
separated by `strideBytes`). -/
structure Strided2DPatch where
  base          : Nat
  strideBytes   : Nat
  rows          : Nat
  rowWidthBytes : Nat

/-- Enumerate the per-row byte intervals of a `Strided2DPatch` via `@Nat.rec`
(`0` `._unsafe_rec`). -/
@[expose] def patchRowIntervals (p : Strided2DPatch) : List ByteInterval :=
  (@Nat.rec (fun _ => Nat → List ByteInterval)
    (fun _ => [])
    (fun _ ih rowIdx =>
      ⟨p.base + rowIdx * p.strideBytes, p.rowWidthBytes⟩ :: ih (rowIdx + 1))
    p.rows) 0

/-- `4 x 4` macroblock sub-block patch (`4` rows x `8` bytes = `4 x u16`
pixels per row) for sub-block index `idx` (`0..15`, `r = idx / 4`,
`c = idx % 4`). -/
@[expose] def subBlockPatch (base strideBytes idx : Nat) : List ByteInterval :=
  let r := Nat.div idx 4
  let c := Nat.mod idx 4
  let subBase := base + (r * 4) * strideBytes + c * 8
  patchRowIntervals ⟨subBase, strideBytes, 4, 8⟩

/-- Pairwise disjointness of two strided patch interval lists (`0`
`._unsafe_rec`). -/
@[expose] def patchesDisjoint (p1 p2 : List ByteInterval) : Bool :=
  intervalsDisjointFromFrames p1 p2

/-- Enumerate all `n` sub-block patches `[0 .. n - 1]` via `@Nat.rec` (`0`
`._unsafe_rec`). -/
@[expose] def allSubBlockPatches (base strideBytes count : Nat) :
    List (List ByteInterval) :=
  (@Nat.rec (fun _ => Nat → List (List ByteInterval))
    (fun _ => [])
    (fun _ ih idx => subBlockPatch base strideBytes idx :: ih (idx + 1))
    count) 0

/-- Check via `List.foldr` that every pair of distinct patches in `ps` is
byte-disjoint (`0` `._unsafe_rec`). -/
@[expose] def allPatchesPairwiseDisjoint
    (ps : List (List ByteInterval)) : Bool :=
  (ps.foldr
    (fun p st =>
      let okHere := st.2.foldr (fun q acc => patchesDisjoint p q && acc) true
      (okHere && st.1, p :: st.2))
    (true, [])).1

/-- Computable disjointness check across all 16 (`4 x 4`) sub-blocks of a
macroblock at `(base, strideBytes)`. -/
@[expose] def allSubBlocksDisjoint (base strideBytes : Nat) : Bool :=
  allPatchesPairwiseDisjoint (allSubBlockPatches base strideBytes 16)

private theorem row_addr_eq (base stride r c k : Nat) :
    (base + (r * 4) * stride + c * 8) + k * stride =
      base + (r * 4 + k) * stride + c * 8 := by
  rw [Nat.add_right_comm, Nat.add_assoc base, ← Nat.add_mul]

private theorem interval_disjoint_same_row (base stride row c1 c2 : Nat)
    (hlt : c1 + 1 ≤ c2) :
    byteIntervalsDisjoint
      ⟨base + row * stride + c1 * 8, 8⟩
      ⟨base + row * stride + c2 * 8, 8⟩ = true := by
  unfold byteIntervalsDisjoint rangesDisjoint
  have hMul : (c1 + 1) * 8 ≤ c2 * 8 := Nat.mul_le_mul_right 8 hlt
  have h1 : c1 * 8 + 8 ≤ c2 * 8 := by
    rw [← Nat.succ_mul]
    exact hMul
  have h2 : (base + row * stride + c1 * 8) + 8 ≤
      base + row * stride + c2 * 8 := by
    rw [Nat.add_assoc (base + row * stride)]
    exact Nat.add_le_add_left h1 (base + row * stride)
  rw [natBle_of_le h2]
  rfl

private theorem interval_disjoint_lt_row (base stride row1 row2 c1 c2 : Nat)
    (hc1 : c1 ≤ 3) (hStride : 32 ≤ stride) (hRow : row1 + 1 ≤ row2) :
    byteIntervalsDisjoint
      ⟨base + row1 * stride + c1 * 8, 8⟩
      ⟨base + row2 * stride + c2 * 8, 8⟩ = true := by
  unfold byteIntervalsDisjoint rangesDisjoint
  have hCol : c1 * 8 + 8 ≤ 32 := by
    have hM : c1 * 8 ≤ 24 := Nat.mul_le_mul_right 8 hc1
    exact Nat.add_le_add_right hM 8
  have hStep1 : (base + row1 * stride + c1 * 8) + 8 ≤
      base + row1 * stride + stride := by
    rw [Nat.add_assoc (base + row1 * stride)]
    exact Nat.add_le_add_left (Nat.le_trans hCol hStride) (base + row1 * stride)
  have hStep2 : base + row1 * stride + stride ≤ base + row2 * stride := by
    rw [Nat.add_assoc base, ← Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right stride hRow) base
  have hStep3 : base + row2 * stride ≤ base + row2 * stride + c2 * 8 :=
    Nat.le_add_right _ _
  rw [natBle_of_le (Nat.le_trans hStep1 (Nat.le_trans hStep2 hStep3))]
  rfl

private theorem subBlockRow_disjoint (base stride r1 c1 k1 r2 c2 k2 : Nat)
    (hc1 : c1 ≤ 3) (hc2 : c2 ≤ 3) (hStride : 32 ≤ stride)
    (hDiff : r1 * 4 + k1 + 1 ≤ r2 * 4 + k2 ∨
             r2 * 4 + k2 + 1 ≤ r1 * 4 + k1 ∨
             (r1 * 4 + k1 = r2 * 4 + k2 ∧ (c1 + 1 ≤ c2 ∨ c2 + 1 ≤ c1))) :
    byteIntervalsDisjoint
      ⟨(base + (r1 * 4) * stride + c1 * 8) + k1 * stride, 8⟩
      ⟨(base + (r2 * 4) * stride + c2 * 8) + k2 * stride, 8⟩ = true := by
  rw [row_addr_eq base stride r1 c1 k1, row_addr_eq base stride r2 c2 k2]
  cases hDiff with
  | inl hLt =>
    exact interval_disjoint_lt_row base stride (r1 * 4 + k1) (r2 * 4 + k2)
      c1 c2 hc1 hStride hLt
  | inr hRest =>
    cases hRest with
    | inl hGt =>
      unfold byteIntervalsDisjoint
      rw [rangesDisjoint_symm]
      exact interval_disjoint_lt_row base stride (r2 * 4 + k2) (r1 * 4 + k1)
        c2 c1 hc2 hStride hGt
    | inr hSame =>
      rw [hSame.1]
      cases hSame.2 with
      | inl hCLt =>
        exact interval_disjoint_same_row base stride (r2 * 4 + k2) c1 c2 hCLt
      | inr hCGt =>
        unfold byteIntervalsDisjoint
        rw [rangesDisjoint_symm]
        exact interval_disjoint_same_row base stride (r2 * 4 + k2) c2 c1 hCGt

private theorem four_row_disjoint_lt (r1 r2 k1 k2 : Nat)
    (hr : r1 + 1 ≤ r2) (hk1 : k1 ≤ 3) :
    r1 * 4 + k1 + 1 ≤ r2 * 4 + k2 := by
  have h1 : r1 * 4 + k1 + 1 ≤ r1 * 4 + 4 := by
    rw [Nat.add_assoc (r1 * 4)]
    exact Nat.add_le_add_left (Nat.succ_le_succ hk1) (r1 * 4)
  have h2 : r1 * 4 + 4 ≤ r2 * 4 := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right 4 hr
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_add_right _ _))

private theorem subBlockRow_disjoint_of_grid
    (base stride r1 c1 k1 r2 c2 k2 : Nat)
    (hc1 : c1 ≤ 3) (hc2 : c2 ≤ 3) (hk1 : k1 ≤ 3) (hk2 : k2 ≤ 3)
    (hStride : 32 ≤ stride)
    (hGrid : r1 + 1 ≤ r2 ∨ r2 + 1 ≤ r1 ∨
      (r1 = r2 ∧ (c1 + 1 ≤ c2 ∨ c2 + 1 ≤ c1))) :
    byteIntervalsDisjoint
      ⟨(base + (r1 * 4) * stride + c1 * 8) + k1 * stride, 8⟩
      ⟨(base + (r2 * 4) * stride + c2 * 8) + k2 * stride, 8⟩ = true := by
  apply subBlockRow_disjoint base stride r1 c1 k1 r2 c2 k2 hc1 hc2 hStride
  cases hGrid with
  | inl hLt => exact Or.inl (four_row_disjoint_lt r1 r2 k1 k2 hLt hk1)
  | inr hRest =>
    cases hRest with
    | inl hGt =>
      exact Or.inr (Or.inl (four_row_disjoint_lt r2 r1 k2 k1 hGt hk2))
    | inr hEqR =>
      rw [hEqR.1]
      cases nat_trichotomy k1 k2 with
      | inl hKLt =>
        exact Or.inl (by
          rw [Nat.add_assoc (r2 * 4)]
          exact Nat.add_le_add_left hKLt (r2 * 4))
      | inr hKRest =>
        cases hKRest with
        | inl hKGt =>
          exact Or.inr (Or.inl (by
            rw [Nat.add_assoc (r2 * 4)]
            exact Nat.add_le_add_left hKGt (r2 * 4)))
        | inr hKEq =>
          rw [hKEq]
          exact Or.inr (Or.inr ⟨rfl, hEqR.2⟩)

private theorem div4_mod4_lt16 (n : Nat) (hn : Nat.blt n 16 = true) :
    Nat.mod n 4 ≤ 3 ∧ Nat.div n 4 * 4 + Nat.mod n 4 = n :=
  match n, hn with
  | 0, _ => ⟨le_of_natBle rfl, rfl⟩
  | 1, _ => ⟨le_of_natBle rfl, rfl⟩
  | 2, _ => ⟨le_of_natBle rfl, rfl⟩
  | 3, _ => ⟨le_of_natBle rfl, rfl⟩
  | 4, _ => ⟨le_of_natBle rfl, rfl⟩
  | 5, _ => ⟨le_of_natBle rfl, rfl⟩
  | 6, _ => ⟨le_of_natBle rfl, rfl⟩
  | 7, _ => ⟨le_of_natBle rfl, rfl⟩
  | 8, _ => ⟨le_of_natBle rfl, rfl⟩
  | 9, _ => ⟨le_of_natBle rfl, rfl⟩
  | 10, _ => ⟨le_of_natBle rfl, rfl⟩
  | 11, _ => ⟨le_of_natBle rfl, rfl⟩
  | 12, _ => ⟨le_of_natBle rfl, rfl⟩
  | 13, _ => ⟨le_of_natBle rfl, rfl⟩
  | 14, _ => ⟨le_of_natBle rfl, rfl⟩
  | 15, _ => ⟨le_of_natBle rfl, rfl⟩
  | _ + 16, h => False.elim (boolFalseNeTrue h)

/-- Symbolic 16-sub-block macroblock disjointness for ALL base addresses, ALL
strides `strideBytes >= 32`, and ALL distinct sub-block indices `i, j < 16`
(`[propext]`). -/
theorem macroblock16_all_strides_ge32_disjoint
    (base strideBytes i j : Nat)
    (hi : Nat.blt i 16 = true)
    (hj : Nat.blt j 16 = true)
    (hne : Nat.beq i j = false)
    (hStride : Nat.ble 32 strideBytes = true) :
    patchesDisjoint (subBlockPatch base strideBytes i)
      (subBlockPatch base strideBytes j) = true := by
  have hI := div4_mod4_lt16 i hi
  have hJ := div4_mod4_lt16 j hj
  have hSt : 32 ≤ strideBytes := le_of_natBle hStride
  have hGrid :
      Nat.div i 4 + 1 ≤ Nat.div j 4 ∨
      Nat.div j 4 + 1 ≤ Nat.div i 4 ∨
      (Nat.div i 4 = Nat.div j 4 ∧
        (Nat.mod i 4 + 1 ≤ Nat.mod j 4 ∨ Nat.mod j 4 + 1 ≤ Nat.mod i 4)) := by
    cases nat_trichotomy (Nat.div i 4) (Nat.div j 4) with
    | inl hLt => exact Or.inl hLt
    | inr hRest =>
      cases hRest with
      | inl hGt => exact Or.inr (Or.inl hGt)
      | inr hEqR =>
        cases nat_trichotomy (Nat.mod i 4) (Nat.mod j 4) with
        | inl hCLt => exact Or.inr (Or.inr ⟨hEqR, Or.inl hCLt⟩)
        | inr hCRest =>
          cases hCRest with
          | inl hCGt => exact Or.inr (Or.inr ⟨hEqR, Or.inr hCGt⟩)
          | inr hEqC =>
            have hEqIJ : i = j := by
              rw [← hI.2, ← hJ.2, hEqR, hEqC]
            rw [hEqIJ, natBeq_refl j] at hne
            exact False.elim (boolFalseNeTrue hne.symm)
  have h0 : (0 : Nat) ≤ 3 := le_of_natBle rfl
  have h1 : (1 : Nat) ≤ 3 := le_of_natBle rfl
  have h2 : (2 : Nat) ≤ 3 := le_of_natBle rfl
  have h3 : (3 : Nat) ≤ 3 := le_of_natBle rfl
  have hPair := fun k1 k2 hk1 hk2 =>
    subBlockRow_disjoint_of_grid base strideBytes
      (Nat.div i 4) (Nat.mod i 4) k1 (Nat.div j 4) (Nat.mod j 4) k2
      hI.1 hJ.1 hk1 hk2 hSt hGrid
  dsimp only [patchesDisjoint, subBlockPatch, patchRowIntervals,
    intervalsDisjointFromFrames, intervalDisjointFromList, List.foldr]
  rw [hPair 0 0 h0 h0, hPair 0 1 h0 h1, hPair 0 2 h0 h2, hPair 0 3 h0 h3,
      hPair 1 0 h1 h0, hPair 1 1 h1 h1, hPair 1 2 h1 h2, hPair 1 3 h1 h3,
      hPair 2 0 h2 h0, hPair 2 1 h2 h1, hPair 2 2 h2 h2, hPair 2 3 h2 h3,
      hPair 3 0 h3 h0, hPair 3 1 h3 h1, hPair 3 2 h3 h2, hPair 3 3 h3 h3]
  rfl

private theorem bandFalseLeft (b : Bool) : (false && b) = false := rfl

private theorem bandFalseRight (b : Bool) : (b && false) = false := by
  cases b <;> rfl

private theorem natBeq_false_of_lt {a b : Nat} (h : a + 1 ≤ b) :
    Nat.beq a b = false := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => cases h
    | succ _ => rfl
  | succ a' ih =>
    intro b h
    cases b with
    | zero => cases h
    | succ b' => exact ih (Nat.le_of_succ_le_succ h)

private def subBlockPatchesFrom (base strideBytes count : Nat) :
    Nat → List (List ByteInterval) :=
  @Nat.rec (fun _ => Nat → List (List ByteInterval))
    (fun _ => [])
    (fun _ ih idx => subBlockPatch base strideBytes idx :: ih (idx + 1))
    count

private theorem allPatchesPairwiseDisjoint_snd
    (ps : List (List ByteInterval)) :
    (ps.foldr
      (fun p st =>
        let okHere := st.2.foldr (fun q acc => patchesDisjoint p q && acc) true
        (okHere && st.1, p :: st.2))
      (true, [])).2 = ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    dsimp only [List.foldr]
    exact congrArg (List.cons p) ih

private theorem allPatchesPairwiseDisjoint_cons
    (p : List ByteInterval) (ps : List (List ByteInterval)) :
    allPatchesPairwiseDisjoint (p :: ps) =
      (ps.foldr (fun q acc => patchesDisjoint p q && acc) true &&
        allPatchesPairwiseDisjoint ps) := by
  unfold allPatchesPairwiseDisjoint
  dsimp only [List.foldr]
  rw [allPatchesPairwiseDisjoint_snd ps]

private theorem patchesDisjoint_subBlockPatchesFrom
    (base strideBytes i : Nat)
    (hi : Nat.blt i 16 = true)
    (hStride : Nat.ble 32 strideBytes = true)
    (k start : Nat) (hLt : i + 1 ≤ start) (hEnd : start + k ≤ 16) :
    (subBlockPatchesFrom base strideBytes k start).foldr
      (fun q acc => patchesDisjoint (subBlockPatch base strideBytes i) q && acc)
      true = true := by
  induction k generalizing start with
  | zero => rfl
  | succ k' ih =>
    change (patchesDisjoint (subBlockPatch base strideBytes i)
      (subBlockPatch base strideBytes start) &&
      (subBlockPatchesFrom base strideBytes k' (start + 1)).foldr
        (fun q acc => patchesDisjoint (subBlockPatch base strideBytes i) q &&
          acc)
        true) = true
    have hStartLt : Nat.blt start 16 = true :=
      natBle_of_le
        (Nat.le_trans
          (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k')) start)
          hEnd)
    have hNe : Nat.beq i start = false := natBeq_false_of_lt hLt
    have hPair := macroblock16_all_strides_ge32_disjoint base strideBytes i
      start hi hStartLt hNe hStride
    have hNextEnd : (start + 1) + k' ≤ 16 := by
      rw [Nat.add_assoc, Nat.add_comm 1 k']
      exact hEnd
    have hTail := ih (start + 1) (Nat.le_trans hLt (Nat.le_succ start)) hNextEnd
    rw [hPair, hTail]
    rfl

private theorem allPatchesPairwiseDisjoint_subBlockPatchesFrom
    (base strideBytes : Nat) (hStride : Nat.ble 32 strideBytes = true)
    (k start : Nat) (hEnd : start + k ≤ 16) :
    allPatchesPairwiseDisjoint
      (subBlockPatchesFrom base strideBytes k start) = true := by
  induction k generalizing start with
  | zero => rfl
  | succ k' ih =>
    change allPatchesPairwiseDisjoint
      (subBlockPatch base strideBytes start ::
        subBlockPatchesFrom base strideBytes k' (start + 1)) = true
    rw [allPatchesPairwiseDisjoint_cons]
    have hStartLt : Nat.blt start 16 = true :=
      natBle_of_le
        (Nat.le_trans
          (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k')) start)
          hEnd)
    have hNextEnd : (start + 1) + k' ≤ 16 := by
      rw [Nat.add_assoc, Nat.add_comm 1 k']
      exact hEnd
    have hHead := patchesDisjoint_subBlockPatchesFrom base strideBytes start
      hStartLt hStride k' (start + 1) (Nat.le_refl (start + 1)) hNextEnd
    have hTail := ih (start + 1) hNextEnd
    rw [hHead, hTail]
    rfl

/-- Universal proof that `allSubBlocksDisjoint base strideBytes = true` for ALL
base addresses and ALL `strideBytes >= 32` (`[propext]`). -/
theorem allSubBlocksDisjoint_of_stride_ge32 (base strideBytes : Nat)
    (hStride : Nat.ble 32 strideBytes = true) :
    allSubBlocksDisjoint base strideBytes = true :=
  allPatchesPairwiseDisjoint_subBlockPatchesFrom base strideBytes hStride
    16 0 (le_of_natBle rfl)

private theorem subBlock0_3_stride24_overlap (base : Nat) :
    patchesDisjoint (subBlockPatch base 24 0) (subBlockPatch base 24 3) =
      false := by
  have hSelf : byteIntervalsDisjoint ⟨base + 24, 8⟩ ⟨base + 24, 8⟩ = false := by
    unfold byteIntervalsDisjoint rangesDisjoint
    have hLt : base + 24 + 1 ≤ base + 24 + 8 :=
      Nat.add_le_add_left (le_of_natBle rfl) (base + 24)
    rw [natBle_false_of_lt hLt]
    rfl
  dsimp only [patchesDisjoint, subBlockPatch, patchRowIntervals,
    intervalsDisjointFromFrames, intervalDisjointFromList, List.foldr]
  have hEq0 :
      base + Nat.div 0 4 * 4 * 24 + Nat.mod 0 4 * 8 + (0 + 1) * 24 =
        base + 24 := by
    rw [Nat.add_zero, Nat.add_zero]
  have hEq3 :
      base + Nat.div 3 4 * 4 * 24 + Nat.mod 3 4 * 8 + 0 * 24 =
        base + 24 := by
    rw [Nat.add_zero, Nat.add_zero]
  rw [hEq0, hEq3, hSelf, bandFalseLeft, bandFalseLeft, bandFalseRight]

/-- Universal rejection of `stride = 24 < 32` for ALL base addresses without
expanding all 120 pairs in kernel WHNF (`[]` axioms). -/
theorem allSubBlocksDisjoint_stride24_false (base : Nat) :
    allSubBlocksDisjoint base 24 = false := by
  change allPatchesPairwiseDisjoint
    (subBlockPatch base 24 0 ::
      subBlockPatch base 24 1 ::
      subBlockPatch base 24 2 ::
      subBlockPatch base 24 3 ::
      subBlockPatchesFrom base 24 12 4) = false
  rw [allPatchesPairwiseDisjoint_cons]
  dsimp only [List.foldr]
  rw [subBlock0_3_stride24_overlap base, bandFalseLeft, bandFalseRight,
      bandFalseRight, bandFalseLeft]

private theorem frames_end_le_mono (a b : Nat) (hLe : a ≤ b)
    (frames : List ByteInterval)
    (hFrames : frames.foldr
      (fun fr acc => Nat.ble (fr.start + fr.len) a && acc) true = true) :
    frames.foldr
      (fun fr acc => Nat.ble (fr.start + fr.len) b && acc) true = true := by
  induction frames with
  | nil => rfl
  | cons fr rest ih =>
    dsimp only [List.foldr] at hFrames
    dsimp only [List.foldr]
    have h1 : Nat.ble (fr.start + fr.len) b = true :=
      natBle_of_le (Nat.le_trans (le_of_natBle (bandLeft hFrames)) hLe)
    rw [h1, ih (bandRight hFrames)]
    rfl

private theorem intervalDisjointFromList_of_below
    (start len : Nat) (frames : List ByteInterval)
    (hFrames : frames.foldr
      (fun fr acc => Nat.ble (fr.start + fr.len) start && acc) true = true) :
    intervalDisjointFromList ⟨start, len⟩ frames = true := by
  induction frames with
  | nil => rfl
  | cons fr rest ih =>
    dsimp only [List.foldr] at hFrames
    change (byteIntervalsDisjoint ⟨start, len⟩ fr &&
      intervalDisjointFromList ⟨start, len⟩ rest) = true
    have hFr := bandLeft hFrames
    have hTail := ih (bandRight hFrames)
    have hDisj : byteIntervalsDisjoint ⟨start, len⟩ fr = true := by
      unfold byteIntervalsDisjoint rangesDisjoint
      rw [hFr, borTrueRight]
    rw [hDisj, hTail]
    rfl

private theorem patchRowIntervals_disjoint_of_below
    (base stride rows rowWidth rowIdx : Nat) (frames : List ByteInterval)
    (hFrames : frames.foldr
      (fun fr acc => Nat.ble (fr.start + fr.len) base && acc) true = true) :
    intervalsDisjointFromFrames
      ((@Nat.rec (fun _ => Nat → List ByteInterval)
        (fun _ => [])
        (fun _ ih r => ⟨base + r * stride, rowWidth⟩ :: ih (r + 1))
        rows) rowIdx)
      frames = true := by
  induction rows generalizing rowIdx with
  | zero => rfl
  | succ k ih =>
    change (intervalDisjointFromList ⟨base + rowIdx * stride, rowWidth⟩
      frames &&
      intervalsDisjointFromFrames
        ((@Nat.rec (fun _ => Nat → List ByteInterval)
          (fun _ => [])
          (fun _ ih r => ⟨base + r * stride, rowWidth⟩ :: ih (r + 1))
          k) (rowIdx + 1))
        frames) = true
    have hHere := intervalDisjointFromList_of_below
      (base + rowIdx * stride) rowWidth frames
      (frames_end_le_mono base (base + rowIdx * stride)
        (Nat.le_add_right base (rowIdx * stride)) frames hFrames)
    rw [hHere, ih (rowIdx + 1)]
    rfl

private theorem subBlockPatchesFrom_disjoint_of_below
    (base strideBytes count start : Nat) (frames : List ByteInterval)
    (hFrames : frames.foldr
      (fun fr acc => Nat.ble (fr.start + fr.len) base && acc) true = true) :
    (subBlockPatchesFrom base strideBytes count start).foldr
      (fun p acc => intervalsDisjointFromFrames p frames && acc) true = true :=
  by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    change (intervalsDisjointFromFrames (subBlockPatch base strideBytes start)
      frames &&
      (subBlockPatchesFrom base strideBytes k (start + 1)).foldr
        (fun p acc => intervalsDisjointFromFrames p frames && acc) true) = true
    have hSubGe :
        base ≤ base + (Nat.div start 4 * 4) * strideBytes +
          Nat.mod start 4 * 8 :=
      Nat.le_trans (Nat.le_add_right base _) (Nat.le_add_right _ _)
    have hPatch :
        intervalsDisjointFromFrames (subBlockPatch base strideBytes start)
          frames = true :=
      patchRowIntervals_disjoint_of_below
        (base + (Nat.div start 4 * 4) * strideBytes + Nat.mod start 4 * 8)
        strideBytes 4 8 0 frames
        (frames_end_le_mono base _ hSubGe frames hFrames)
    rw [hPatch, ih (start + 1)]
    rfl

/-- Concrete `stride = 32` and `stride = 64` admission paired with single-cause
`stride = 24 < 32` cross-row overlap rejection (`[propext]`). -/
theorem macroblock16_stride32_all_disjoint :
    allSubBlocksDisjoint 0x10000 32 = true ∧
    allSubBlocksDisjoint 0x10000 64 = true ∧
    allSubBlocksDisjoint 0x10000 24 = false :=
  ⟨allSubBlocksDisjoint_of_stride_ge32 0x10000 32 rfl,
   allSubBlocksDisjoint_of_stride_ge32 0x10000 64 rfl,
   allSubBlocksDisjoint_stride24_false 0x10000⟩

/-- All 16 sub-block patches in a `stride = 32` macroblock placed above a
caller stack frame (`[entrySp, entrySp + 64)`) are strictly disjoint from both
the caller frame and the return-address slot `[entrySp, entrySp + 8)`, and
committing writes into a full `512`-byte exposed macroblock allocation leaves
an unexposed caller-frame MIR allocation identically preserved (`[propext]`).
-/
theorem macroblock16_caller_frame_preserved :
    let entrySp : Nat := 65536
    let retSlot : ByteInterval := ⟨entrySp, 8⟩
    let callerFrame : ByteInterval := ⟨entrySp, 64⟩
    let mbBase : Nat := entrySp + 64
    let patches := allSubBlockPatches mbBase 32 16
    let allDisjFromCaller :=
      patches.foldr
        (fun p acc => intervalsDisjointFromFrames p [retSlot, callerFrame] &&
          acc)
        true
    let callerAlloc : Allocation :=
      { allocId := 10, alignLog2 := 3, mutability := .mut,
        bytes := [.init 0xDE (some 1), .uninit, .init 0xAD none],
        live := true }
    let mbAlloc : Allocation :=
      { allocId := 20, alignLog2 := 4, mutability := .mut,
        bytes := replicateAllocByte 512 (.init 0 none),
        live := true }
    let mem : MemoryState :=
      { nextAllocId := 21, allocations := [callerAlloc, mbAlloc] }
    let exposed : List ExposedMirAlloc := [⟨20, mbBase⟩]
    let writes := mkByteWrites mbBase [1, 2, 3, 4, 5, 6, 7, 8]
    mbAlloc.bytes.length = 512 ∧
    allSubBlocksDisjoint mbBase 32 = true ∧
    allDisjFromCaller = true ∧
    ∀ m', commitMachineByteWrites mem exposed writes = some m' →
      lookupMirAlloc 10 m' = some callerAlloc := by
  refine ⟨replicateAllocByte_length 512 (.init 0 none),
          allSubBlocksDisjoint_of_stride_ge32 (65536 + 64) 32 rfl,
          subBlockPatchesFrom_disjoint_of_below (65536 + 64) 32 16 0
            [⟨65536, 8⟩, ⟨65536, 64⟩] rfl,
          ?_⟩
  intro m' hCommit
  exact commitMachineByteWrites_preserves_unexposed _ _ m' _ 10 rfl hCommit

end Anneal.AsmBridge.MemoryWindow

end
