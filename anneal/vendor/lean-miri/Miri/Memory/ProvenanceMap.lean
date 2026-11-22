import Miri.Memory.QSortProof
import Miri.Memory.AllocRange
import Miri.Memory.CtfeProvenance

/-!
The pointer-sized and byte-fragment representation from rustc's pinned
allocation/provenance_map.rs. Read operations preserve the distinction between
no provenance, wildcard provenance, and a partial CTFE pointer error.
The checked construction below enforces sorted unique map keys. It does not
replace the allocation's bounds/initialization/aliasing checks.
-/

namespace Miri.Memory

open Miri.ABI

structure PointerFrag (Prov : Type u) where
  idx : UInt8
  prov : Prov
  bytes : Vector UInt8 8
  deriving DecidableEq, Repr

inductive ProvenanceMapError where
  | memory (reason : MemoryError)
  | pointerSizeZero
  | unsortedOrDuplicateKeys
  | readPartialPointer (offset : Size)
  | missingWildcard
  | pointerSizedProvenanceAtByte (offset : Size)
  | insertOverlapsExistingProvenance
  | pointerSizeExceedsFragmentStorage (bytes : UInt64)
  | fragmentSliceOutOfBounds (start size : Size) (available : Nat)
  | copyEntryCountOverflow
  deriving DecidableEq, Repr

structure ProvenanceMap (Prov : Type u) where
  private mk ::
  ptrs : Array (Size × Prov)
  byteFragments : Option (Array (Size × PointerFrag Prov))
  deriving DecidableEq, Repr

structure ProvenanceCopy (Prov : Type u) where
  ptrs : Array (Size × Prov)
  byteFragments : Array (Size × PointerFrag Prov)
  deriving DecidableEq, Repr

namespace ProvenanceMap

def new : ProvenanceMap Prov := ⟨#[], none⟩

private def sortedKeys (values : List (Size × α)) : Bool :=
  match values with
  | [] | [_] => true
  | (left, _) :: tail@((right, _) :: _) =>
      left.bytes < right.bytes && sortedKeys tail

/-- The source requires sorted, duplicate-free keys at this entry point. -/
def fromPresortedPtrs (values : Array (Size × Prov)) : Except ProvenanceMapError (ProvenanceMap Prov) :=
  if sortedKeys values.toList then .ok ⟨values, none⟩
  else .error .unsortedOrDuplicateKeys

/-- A fragment-state decoder with the same sorted-map key invariants. It is
not a replacement for source `prepare_copy`/`apply_copy`/`clear` operations. -/
def fromParts (ptrs : Array (Size × Prov))
    (fragments : Option (Array (Size × PointerFrag Prov))) : Except ProvenanceMapError (ProvenanceMap Prov) :=
  if sortedKeys ptrs.toList && (fragments.map fun entries => sortedKeys entries.toList).getD true then
    .ok ⟨ptrs, fragments⟩
  else .error .unsortedOrDuplicateKeys

def getPtr (self : ProvenanceMap Prov) (offset : Size) : Option Prov :=
  (self.ptrs.find? fun entry => entry.1.bytes == offset.bytes).map Prod.snd

private def rangeEntries (values : Array (Size × α)) (start finish : Size) : Array (Size × α) :=
  values.filter fun entry => start.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes

private def adjustedStart (range : AllocRange) (pointerSize : Size) : Except ProvenanceMapError Size :=
  if pointerSize.bytes == 0 then .error .pointerSizeZero
  else .ok (Size.ofBytes (UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat - 1))))

private def rangeEnd (range : AllocRange) : Except ProvenanceMapError Size :=
  range.endExclusive.mapError .memory

def rangePtrs (self : ProvenanceMap Prov) (range : AllocRange) (pointerSize : Size) :
    Except ProvenanceMapError (Array (Size × Prov)) := do
  let start ← adjustedStart range pointerSize
  let finish ← rangeEnd range
  return rangeEntries self.ptrs start finish

def rangeBytes (self : ProvenanceMap Prov) (range : AllocRange) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) := do
  let finish ← rangeEnd range
  return rangeEntries (self.byteFragments.getD #[]) range.start finish

def rangeEmpty (self : ProvenanceMap Prov) (range : AllocRange) (pointerSize : Size) :
    Except ProvenanceMapError Bool := do
  let ptrs ← self.rangePtrs range pointerSize
  if !ptrs.isEmpty then return false
  return (← self.rangeBytes range).isEmpty

def getByte (self : ProvenanceMap Prov) (offset pointerSize : Size) :
    Except ProvenanceMapError (Option (PointerFrag Prov)) := do
  let overlapping ← self.rangePtrs ⟨offset, Size.ofBytes 1⟩ pointerSize
  if !overlapping.isEmpty then throw (.pointerSizedProvenanceAtByte offset)
  return ((self.byteFragments.getD #[]).find? fun entry => entry.1.bytes == offset.bytes).map Prod.snd

/-- Source `get_range` yields whole pointer entries first, then byte entries. -/
def getRange (self : ProvenanceMap Prov) (range : AllocRange) (pointerSize : Size) :
    Except ProvenanceMapError (Array (AllocRange × Prov)) := do
  let ptrs ← self.rangePtrs range pointerSize
  let fragments ← self.rangeBytes range
  return (ptrs.map fun (offset, prov) => (allocRange offset pointerSize, prov)) ++
    (fragments.map fun (offset, frag) => (allocRange offset (Size.ofBytes 1), frag.prov))

def provenances (self : ProvenanceMap Prov) : Array Prov :=
  (self.ptrs.map Prod.snd) ++ ((self.byteFragments.getD #[]).map fun (_, frag) => frag.prov)

private def inspectFragments [DecidableEq Prov] [PointerProvenance Prov]
    (self : ProvenanceMap Prov) (offset pointerSize : Size) :
    Except ProvenanceMapError (Option Prov) := do
  let mut expected : Option (Prov × Vector UInt8 8) := none
  for idx in [:pointerSize.bytes.toNat] do
    let position ← (Size.add offset (Size.ofBytes (UInt64.ofNat idx))).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
    let fragment ← self.getByte position pointerSize
    let some frag := fragment | return none
    if some frag.prov == PointerProvenance.wildcard (Prov := Prov) then continue
    if frag.idx.toNat != idx then return none
    match expected with
    | some pair =>
        if (frag.prov, frag.bytes) != pair then return none
    | none => expected := some (frag.prov, frag.bytes)
  match expected with
  | some (prov, _) => return some prov
  | none =>
      match PointerProvenance.wildcard (Prov := Prov) with
      | some wildcard => return some wildcard
      | none => throw .missingWildcard

def readPtr [DecidableEq Prov] [PointerProvenance Prov]
    (self : ProvenanceMap Prov) (offset pointerSize : Size) :
    Except ProvenanceMapError (Option Prov) := do
  if let some prov := self.getPtr offset then return some prov
  let range := allocRange offset pointerSize
  let ptrs ← self.rangePtrs range pointerSize
  let fragments ← self.rangeBytes range
  if ptrs.isEmpty && fragments.isEmpty then return none
  let prov ← if ptrs.isEmpty then self.inspectFragments offset pointerSize else pure none
  if prov.isNone && !PointerProvenance.offsetIsAddr (Prov := Prov) then
    throw (.readPartialPointer offset)
  return prov

theorem empty_has_no_provenance : provenances (new : ProvenanceMap Prov) = #[] := by
  simp [provenances, new]

theorem read_exact_pointer [DecidableEq Prov] [PointerProvenance Prov]
    (self : ProvenanceMap Prov) (offset pointerSize : Size) (prov : Prov)
    (h : self.getPtr offset = some prov) : self.readPtr offset pointerSize = .ok (some prov) := by
  simp [readPtr, h]
  rfl

/-! Mutating source operations keep the updated state even on assertion
failure, using the standard library's `EStateM` result representation. -/

abbrev Mutation (Prov : Type) (α : Type) := EStateM ProvenanceMapError (ProvenanceMap Prov) α

private def checked (result : Except ProvenanceMapError α) : Mutation Prov α :=
  fun state => match result with
    | .ok value => .ok value state
    | .error reason => .error reason state

private def insertEntry (values : Array (Size × α)) (offset : Size) (value : α) : Array (Size × α) :=
  ((values.filter fun entry => entry.1.bytes != offset.bytes).push (offset, value)).qsort
    (fun left right => left.1.bytes < right.1.bytes)

private def removeEntries (values : Array (Size × α)) (start finish : Size) : Array (Size × α) :=
  values.filter fun entry => !(start.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes)

def insertPtr (offset : Size) (prov : Prov) (pointerSize : Size) : Mutation Prov Unit := do
  let self ← EStateM.get
  if !(← checked (self.rangeEmpty (allocRange offset pointerSize) pointerSize)) then
    throw .insertOverlapsExistingProvenance
  EStateM.set { self with ptrs := insertEntry self.ptrs offset prov }

private def ptrFragments (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (pointerSize : Size) : Except ProvenanceMapError (Array (Size × PointerFrag Prov)) := do
  if pointerSize.bytes > 8 then throw (.pointerSizeExceedsFragmentStorage pointerSize.bytes)
  let finish ← (Size.add position pointerSize).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
  if h : position.bytes.toNat + pointerSize.bytes.toNat ≤ data.size then
    let bytes : Vector UInt8 8 := Vector.ofFn fun index =>
      if hi : index.val < pointerSize.bytes.toNat then
        data[position.bytes.toNat + index.val]'(by omega)
      else 0
    let mut fragments := #[]
    for index in [:pointerSize.bytes.toNat] do
      let pos := Size.ofBytes (position.bytes + UInt64.ofNat index)
      if inRange pos then
        fragments := fragments.push (pos, ⟨UInt8.ofNat index, prov, bytes⟩)
    return fragments
  else throw (.fragmentSliceOutOfBounds position pointerSize data.size)

def clear (range : AllocRange) (data : Array UInt8) (pointerSize : Size) : Mutation Prov Unit := do
  if range.size.bytes == 0 then return ()
  let finish ← checked (rangeEnd range)
  let self ← EStateM.get
  EStateM.set { self with byteFragments := self.byteFragments.map fun bytes => removeEntries bytes range.start finish }
  let self ← EStateM.get
  let ptrs ← checked (self.rangePtrs range pointerSize)
  if ptrs.isEmpty then return ()
  if let some (first, prov) := ptrs[0]? then
    if first.bytes < range.start.bytes then
      let fragments ← checked (ptrFragments (fun pos => pos.bytes < range.start.bytes) first prov data pointerSize)
      let current ← EStateM.get
      let bytes := fragments.foldl (fun values entry => insertEntry values entry.1 entry.2) (current.byteFragments.getD #[])
      EStateM.set { current with byteFragments := some bytes }
  if let some (last, prov) := ptrs.back? then
    let lastEnd ← checked ((Size.add last pointerSize).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError))
    if lastEnd.bytes > finish.bytes then
      let fragments ← checked (ptrFragments (fun pos => finish.bytes ≤ pos.bytes) last prov data pointerSize)
      let current ← EStateM.get
      let bytes := fragments.foldl (fun values entry => insertEntry values entry.1 entry.2) (current.byteFragments.getD #[])
      EStateM.set { current with byteFragments := some bytes }
  let start ← checked (adjustedStart range pointerSize)
  let current ← EStateM.get
  EStateM.set { current with ptrs := removeEntries current.ptrs start finish }

def writeWildcards [PointerProvenance Prov] (range : AllocRange) (data : Array UInt8)
    (pointerSize : Size) : Mutation Prov Unit := do
  let some wildcard := PointerProvenance.wildcard (Prov := Prov) | throw .missingWildcard
  clear range data pointerSize
  let finish ← checked (rangeEnd range)
  let current ← EStateM.get
  let mut bytes := current.byteFragments.getD #[]
  for position in [range.start.bytes.toNat:finish.bytes.toNat] do
    bytes := insertEntry bytes (Size.ofBytes (UInt64.ofNat position))
      ⟨0, wildcard, Vector.replicate 8 0⟩
  EStateM.set { current with byteFragments := some bytes }

def mergeBytes [DecidableEq Prov] (pointerSize : Size) : Mutation Prov Bool := do
  let original ← EStateM.get
  let some bytes := original.byteFragments | return true
  if !bytes.isEmpty && pointerSize.bytes == 0 then throw .pointerSizeZero
  -- Each successful iteration removes at least one fragment. A bounded loop
  -- over the initial byte-map cardinality is therefore sufficient.
  for _ in [:bytes.size] do
    let current ← EStateM.get
    let remaining := current.byteFragments.getD #[]
    let some (offset, first) := remaining[0]? | break
    let finish ← checked ((Size.add offset pointerSize).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError))
    let frags := rangeEntries remaining offset finish
    if frags.size != pointerSize.bytes.toNat then return false
    for index in [:frags.size] do
      let some (_, frag) := frags[index]? | throw .unsortedOrDuplicateKeys
      if frag.prov != first.prov || frag.bytes != first.bytes || frag.idx != UInt8.ofNat index then
        return false
    EStateM.set { current with
      ptrs := insertEntry current.ptrs offset first.prov
      byteFragments := some (removeEntries remaining offset finish) }
  let current ← EStateM.get
  EStateM.set { current with byteFragments := none }
  return true

private def subtractSize (left right : Size) : Except ProvenanceMapError Size :=
  (Size.sub left right).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)

def prepareCopy (self : ProvenanceMap Prov) (range : AllocRange) (data : Array UInt8)
    (pointerSize : Size) : Except ProvenanceMapError (ProvenanceCopy Prov) := do
  if pointerSize.bytes == 0 then throw .pointerSizeZero
  let finish ← rangeEnd range
  let mut ptrs := #[]
  if range.size.bytes ≥ pointerSize.bytes then
    let adjustedEnd ← subtractSize finish (Size.ofBytes (pointerSize.bytes - 1))
    for (offset, prov) in rangeEntries self.ptrs range.start adjustedEnd do
      ptrs := ptrs.push (← subtractSize offset range.start, prov)
  let beginOverlap := (← self.rangePtrs (allocRange range.start Size.ZERO) pointerSize)[0]?
  let endOverlap := (← self.rangePtrs (allocRange finish Size.ZERO) pointerSize)[0]?
  let mut bytes := #[]
  if beginOverlap.isSome || endOverlap.isSome || self.byteFragments.isSome then
    if let some (position, prov) := beginOverlap then
      let ptrEnd ← (Size.add position pointerSize).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
      let fragmentEnd := if ptrEnd.bytes < finish.bytes then ptrEnd else finish
      if range.start.bytes < fragmentEnd.bytes then
        let fragments ← ptrFragments (fun pos => range.start.bytes ≤ pos.bytes && pos.bytes < fragmentEnd.bytes) position prov data pointerSize
        for (pos, frag) in fragments do
          bytes := bytes.push (← subtractSize pos range.start, frag)
    for (offset, frag) in (← self.rangeBytes range) do
      bytes := bytes.push (← subtractSize offset range.start, frag)
    if let some (position, prov) := endOverlap then
      if (beginOverlap.map fun (begin, _) => begin.bytes != position.bytes).getD true then
        if position.bytes < range.start.bytes then throw .unsortedOrDuplicateKeys
        if position.bytes < finish.bytes then
          let fragments ← ptrFragments (fun pos => position.bytes ≤ pos.bytes && pos.bytes < finish.bytes) position prov data pointerSize
          for (pos, frag) in fragments do
            let shifted ← subtractSize pos range.start
            if !((bytes.back?.map fun last => decide (last.1.bytes < shifted.bytes)).getD true) then
              throw .unsortedOrDuplicateKeys
            bytes := bytes.push (shifted, frag)
  return ⟨ptrs, bytes⟩

private def shiftedCopyOffset (range : AllocRange) (index : UInt64) (offset : Size) :
    Except ProvenanceMapError Size := do
  let start ← (Size.add offset range.start).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
  let delta ← (Size.mul range.size index).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
  (Size.add start delta).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)

/-- Source `apply_copy` requires the affected range to have been cleared. The
map insertions retain the source's replacement behavior at existing keys. -/
def applyCopy (copy : ProvenanceCopy Prov) (range : AllocRange) (repeatCount : UInt64) : Mutation Prov Unit := do
  if !copy.ptrs.isEmpty then
    if copy.ptrs.size * repeatCount.toNat ≥ 2 ^ 64 then
      throw .copyEntryCountOverflow
    for index in [:repeatCount.toNat] do
      for (offset, prov) in copy.ptrs do
        let shifted ← checked (shiftedCopyOffset range (UInt64.ofNat index) offset)
        let current ← EStateM.get
        EStateM.set { current with ptrs := insertEntry current.ptrs shifted prov }
  if !copy.byteFragments.isEmpty then
    let current ← EStateM.get
    EStateM.set { current with byteFragments := some (current.byteFragments.getD #[]) }
    if copy.byteFragments.size * repeatCount.toNat ≥ 2 ^ 64 then
      throw .copyEntryCountOverflow
    for index in [:repeatCount.toNat] do
      for (offset, frag) in copy.byteFragments do
        let shifted ← checked (shiftedCopyOffset range (UInt64.ofNat index) offset)
        let current ← EStateM.get
        EStateM.set { current with byteFragments := some (insertEntry (current.byteFragments.getD #[]) shifted frag) }

end ProvenanceMap

end Miri.Memory

namespace Miri.Memory.ProvenanceMap
open Miri.ABI
set_option autoImplicit false
variable {P : Type}
theorem clear_new (range : AllocRange) (data : Array UInt8) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0) (endEq : range.endExclusive = .ok finish) :
    clear range data pointerSize (new (Prov := P)) = .ok () new := by
  unfold clear
  by_cases zero : range.size.bytes = 0
  · simp [zero,pure,Pure.pure,EStateM.pure]
  · simp only [zero,beq_iff_eq,Bool.false_eq_true,↓reduceIte]
    unfold rangePtrs rangeEnd adjustedStart rangeEntries checked
    simp only [endEq,positive,↓reduceIte]
    simp [new,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,EStateM.get,EStateM.set,Except.mapError,Except.bind,Except.pure,positive,zero]
end Miri.Memory.ProvenanceMap

namespace Miri.Memory.ProvenanceMap
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {P : Type}
private theorem empty_range (range : AllocRange) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0) (endEq : range.endExclusive = .ok finish) :
    (new (Prov := P)).rangeEmpty range pointerSize = .ok true := by
  unfold rangeEmpty rangePtrs rangeBytes adjustedStart rangeEnd rangeEntries
  simp [new,positive,endEq,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.mapError]

theorem insertPtr_new (offset pointerSize finish : Size) (provenance : P)
    (positive : pointerSize.bytes ≠ 0) (endEq : (allocRange offset pointerSize).endExclusive = .ok finish) :
    insertPtr offset provenance pointerSize (new (Prov := P)) = .ok () ⟨#[(offset,provenance)],none⟩ := by
  unfold insertPtr
  have empty := empty_range (P := P) (allocRange offset pointerSize) pointerSize finish positive endEq
  simp only [new] at empty
  simp [checked,empty,new,insertEntry,bind,Bind.bind,EStateM.bind,EStateM.get,EStateM.set,
    pure,Pure.pure,EStateM.pure]
  simp [Array.filter_empty,Miri.Memory.QSortProof.singleton]

private theorem singleton_before_range (range : AllocRange) (pointerSize finish : Size) (provenance : P)
    (positive : pointerSize.bytes ≠ 0) (before : pointerSize.bytes.toNat ≤ range.start.bytes.toNat)
    (endEq : range.endExclusive = .ok finish) :
    (⟨#[(Size.ZERO,provenance)],none⟩ : ProvenanceMap P).rangePtrs range pointerSize = .ok #[] := by
  have ptrNatPositive : 0 < pointerSize.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero
    exact positive (UInt64.toNat_inj.mp zero))
  have differencePositive : 0 < range.start.bytes.toNat - (pointerSize.bytes.toNat-1) := by omega
  have fits : range.start.bytes.toNat - (pointerSize.bytes.toNat-1) < 2^64 := by
    have := range.start.bytes.toNat_lt
    omega
  have adjustedPositive : 0 < (UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat-1))).toNat := by
    simpa only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits] using differencePositive
  have notBelow : ¬ UInt64.ofNat (range.start.bytes.toNat - (pointerSize.bytes.toNat-1)) ≤ 0 := by
    simp only [UInt64.le_iff_toNat_le,UInt64.toNat_zero]
    omega
  unfold rangePtrs adjustedStart rangeEnd rangeEntries
  simp [positive,endEq,Size.ZERO,Size.ofBytes,notBelow,bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure]

 theorem clear_singleton_before (range : AllocRange) (data : Array UInt8) (pointerSize finish : Size) (provenance : P)
    (positive : pointerSize.bytes ≠ 0) (before : pointerSize.bytes.toNat ≤ range.start.bytes.toNat)
    (endEq : range.endExclusive = .ok finish) :
    clear range data pointerSize (⟨#[(Size.ZERO,provenance)],none⟩ : ProvenanceMap P) =
      .ok () ⟨#[(Size.ZERO,provenance)],none⟩ := by
  have noPointers := singleton_before_range range pointerSize finish provenance positive before endEq
  unfold clear
  by_cases zero : range.size.bytes = 0
  · simp [zero,pure,Pure.pure,EStateM.pure]
  · simp only [zero,beq_iff_eq,↓reduceIte]
    unfold rangeEnd checked
    simp [endEq,noPointers,bind,Bind.bind,EStateM.bind,EStateM.get,EStateM.set,
      pure,Pure.pure,EStateM.pure,Except.mapError,zero]

theorem insertPtr_singleton_after (offset pointerSize finish : Size) (old newProvenance : P)
    (positive : pointerSize.bytes ≠ 0) (before : pointerSize.bytes.toNat ≤ offset.bytes.toNat)
    (endEq : (allocRange offset pointerSize).endExclusive = .ok finish) :
    ∃ updated, insertPtr offset newProvenance pointerSize
      (⟨#[(Size.ZERO,old)],none⟩ : ProvenanceMap P) = .ok () updated := by
  have noPointers := singleton_before_range (allocRange offset pointerSize) pointerSize finish old positive before endEq
  have empty : (⟨#[(Size.ZERO,old)],none⟩ : ProvenanceMap P).rangeEmpty (allocRange offset pointerSize) pointerSize =
      .ok true := by
    unfold rangeEmpty
    rw [noPointers]
    simp [rangeBytes,rangeEnd,rangeEntries,endEq,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.mapError]
  refine ⟨⟨insertEntry #[(Size.ZERO,old)] offset newProvenance,none⟩,?_⟩
  unfold insertPtr
  simp [checked,empty,bind,Bind.bind,EStateM.bind,EStateM.get,EStateM.set,pure,Pure.pure,EStateM.pure]

end Miri.Memory.ProvenanceMap
