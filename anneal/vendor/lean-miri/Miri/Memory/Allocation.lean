import Miri.Memory.NativeBuffer
import Miri.Memory.InitMask
import Miri.Memory.ProvenanceMap
import Miri.Memory.Scalar
import Miri.ABI.Align

/-!
The source-level allocation record and checked read-byte operations from the
pinned `rustc_middle::mir::interpret::allocation` module. The byte backend is
represented by `Array UInt8`; host allocation is an explicit callback at the
fallible constructor boundary.
-/

namespace Miri.Memory

open Miri.ABI

inductive Mutability where
  | Not
  | Mut
  deriving DecidableEq, Repr

inductive AllocInit where
  | Uninit
  | Zero
  deriving DecidableEq, Repr

structure BadBytesAccess where
  access : AllocRange
  bad : AllocRange
  deriving DecidableEq, Repr

inductive AllocError where
  | readPointerAsInt (info : Option BadBytesAccess)
  | readPartialPointer (offset : Size)
  | invalidUninitBytes (info : Option BadBytesAccess)
  | memory (reason : MemoryError)
  | provenance (reason : ProvenanceMapError)
  | alignment (reason : AlignError)
  | storageLengthOverflow (length : Nat)
  | storageLengthMismatch (requested : Size) (actual : Nat)
  | storageBackendNotZeroed (index : Nat) (value : UInt8)
  | outOfBounds (range : AllocRange) (allocationSize : Size)
  | invalidSliceEndpoints (start finish available : Nat)
  | nonEmptyProvenanceWithoutEntry
  | readOnlyAllocation
  | pointerSizeMismatch (scalarSize pointerSize : Size)
  | scalar (reason : ScalarError)
  | scalarBytesTooWide (size : Size)
  | pointerBitsDoNotFitOffset (bits : U128)
  | scalarPointerNotTargetSized (scalarSize targetSize : Size)
  | copyRangesOverlap
  | repeatedCopyRequiresNonoverlapping
  | singleByteZeroCountCopy
  | allocationHasByteFragmentProvenance
  | nativeWriteRangeOutOfBounds (range : AllocRange) (allocationSize : Size)
  | hostMemoryExhausted
  deriving DecidableEq, Repr

inductive AllocationAdjustError (CallbackError : Type) where
  | allocation (reason : AllocError)
  | byteConversion (reason : CallbackError)
  | pointerAdjustment (reason : CallbackError)
  deriving DecidableEq, Repr

private def provenanceErrorText : ProvenanceMapError → String
  | .memory reason => toString reason
  | .pointerSizeZero => "zero-sized target pointer"
  | .unsortedOrDuplicateKeys => "unsorted or duplicate provenance keys"
  | .readPartialPointer offset => s!"partial pointer at {offset.bytes}"
  | .missingWildcard => "missing wildcard provenance"
  | .pointerSizedProvenanceAtByte offset => s!"pointer-sized provenance at byte {offset.bytes}"
  | .insertOverlapsExistingProvenance => "provenance insertion overlaps an existing pointer"
  | .pointerSizeExceedsFragmentStorage bytes =>
      s!"pointer size {bytes} exceeds the supported fragment byte count"
  | .fragmentSliceOutOfBounds start size available =>
      s!"fragment byte slice starts at {start.bytes} with size {size.bytes}, beyond {available} bytes"
  | .copyEntryCountOverflow => "provenance copy entry count exceeds the supported host index range"

instance : ToString ProvenanceMapError where
  toString := provenanceErrorText

instance : ToString AllocError where
  toString
    | .readPointerAsInt _ => "allocation read encountered pointer provenance where bytes were required"
    | .readPartialPointer offset => s!"allocation read encountered a partial pointer at {offset.bytes}"
    | .invalidUninitBytes _ => "allocation read encountered uninitialized bytes"
    | .memory reason => toString reason
    | .provenance reason => s!"provenance-map error: {reason}"
    | .alignment reason => s!"alignment error: {reason}"
    | .storageLengthOverflow length => s!"byte length {length} does not fit in rustc Size"
    | .storageLengthMismatch requested actual =>
        s!"zeroed storage has {actual} bytes, but {requested.bytes} were requested"
    | .storageBackendNotZeroed index value =>
        s!"zeroed-storage backend returned byte {value} at index {index}"
    | .outOfBounds range allocationSize =>
        s!"byte range starting at {range.start.bytes} with length {range.size.bytes} is outside allocation size {allocationSize.bytes}"
    | .invalidSliceEndpoints start finish available =>
        s!"slice [{start}..{finish}] is outside {available} stored bytes"
    | .nonEmptyProvenanceWithoutEntry =>
        "provenance map reported a nonempty overlap without yielding an entry"
    | .readOnlyAllocation => "cannot mutate an immutable allocation"
    | .pointerSizeMismatch scalarSize pointerSize =>
        s!"pointer scalar size {scalarSize.bytes} differs from target pointer size {pointerSize.bytes}"
    | .scalar reason => s!"scalar error: {reason}"
    | .scalarBytesTooWide size => s!"{size.bytes}-byte scalar exceeds the 16-byte integer width"
    | .pointerBitsDoNotFitOffset bits => s!"pointer bits {bits.toNat} do not fit a u64 offset"
    | .scalarPointerNotTargetSized scalarSize targetSize =>
        s!"pointer scalar size {scalarSize.bytes} differs from target pointer size {targetSize.bytes}"
    | .copyRangesOverlap => "nonoverlapping memory copy received overlapping source and destination ranges"
    | .repeatedCopyRequiresNonoverlapping => "repeated memory copies require nonoverlapping mode"
    | .singleByteZeroCountCopy => "single-byte repeated copy asserted a nonzero copy count"
    | .allocationHasByteFragmentProvenance =>
        "CTFE allocation adjustment requires interned pointer-only provenance"
    | .nativeWriteRangeOutOfBounds range allocationSize =>
        s!"native-write range starting at {range.start.bytes} with length {range.size.bytes} is outside allocation size {allocationSize.bytes}"
    | .hostMemoryExhausted => "host allocation failed while creating the rustc allocation"

private def maxU64Nat : Nat := 18446744073709551615

private def checkedAlign (align : Align) : Except AllocError Align := do
  let bytes ← (Align.bytes align).mapError AllocError.alignment
  let normalized ← (Align.fromBytes bytes).mapError AllocError.alignment
  if normalized == align then return align
  throw (.alignment (.tooLarge bytes))

private def sizeForArray (length : Nat) : Except AllocError Size := do
  if length > maxU64Nat then throw (.storageLengthOverflow length)
  let size := Size.ofBytes (UInt64.ofNat length)
  if size.bytes.toNat == length then return size
  throw (.storageLengthOverflow length)

private def pointerSize (layout : TargetDataLayout) : Size :=
  Size.fromBits layout.pointerWidth.bits

private def targetUIntBytes (layout : TargetDataLayout) (size : Size) (bits : U128) :
    Except AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def readTargetUInt (layout : TargetDataLayout) (bytes : Array UInt8) :
    Except AllocError U128 := do
  if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def firstNonZero (bytes : Array UInt8) : Option (Nat × UInt8) := Id.run do
  for index in [:bytes.size] do
    match bytes[index]? with
    | some byte => if byte != 0 then return some (index, byte)
    | none => return some (index, 0)
  return none

structure Allocation (Prov : Type := CtfeProvenance) (Extra : Type := Unit) where
  private mk ::
  private rawBytes : Array UInt8
  private size : Size
  private provenance : ProvenanceMap Prov
  private initMask : InitMask
  align : Align
  mutability : Mutability
  extra : Extra
  nativeBuffer : Option NativeBufferOwnership := none

namespace Allocation

def fromBytes (bytes : Array UInt8) (align : Align) (mutability : Mutability) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if _h : bytes.size = size.bytes.toNat then
    return ⟨bytes, size, ProvenanceMap.new, InitMask.new size true,
      align, mutability, (), none⟩
  else
    throw (.storageLengthOverflow bytes.size)

def fromBytesByteAlignedImmutable (bytes : Array UInt8) :
    Except AllocError (Allocation Prov Unit) :=
  fromBytes bytes Align.ONE .Not

/-- `zeroedStorage` is the explicit host `AllocBytes::zeroed` boundary. A
`none` result preserves the source's `MemoryExhausted` failure. The backend's
zeroed-storage contract is checked before an allocation value is returned. -/
def tryNew (size : Size) (align : Align) (init : AllocInit)
    (zeroedStorage : Size → Align → Option (Array UInt8)) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let bytes ← match zeroedStorage size align with
    | some bytes => pure bytes
    | none => throw .hostMemoryExhausted
  if bytes.size != size.bytes.toNat then
    throw (.storageLengthMismatch size bytes.size)
  if let some (index, value) := firstNonZero bytes then
    throw (.storageBackendNotZeroed index value)
  let initialized := match init with
    | .Uninit => false
    | .Zero => true
  if _h : bytes.size = size.bytes.toNat then
    return ⟨bytes, size, ProvenanceMap.new, InitMask.new size initialized,
      align, .Mut, (), none⟩
  else
    throw (.storageLengthMismatch size bytes.size)

def withExtra (allocation : Allocation Prov Unit) (extra : Extra) :
    Allocation Prov Extra :=
  ⟨allocation.rawBytes, allocation.size,
    allocation.provenance, allocation.initMask, allocation.align,
    allocation.mutability, extra, allocation.nativeBuffer⟩

/-- Map only allocation metadata. Byte storage, size, provenance, init mask,
alignment, and mutability are copied unchanged, matching the source fieldwise
metadata update boundary used by tree-retagging. -/
def mapExtra (allocation : Allocation Prov Extra) (f : Extra → Extra') :
    Allocation Prov Extra' :=
  ⟨allocation.rawBytes, allocation.size, allocation.provenance,
    allocation.initMask, allocation.align, allocation.mutability,
    f allocation.extra, allocation.nativeBuffer⟩

/-- Replace only allocation metadata while retaining all allocation storage
and semantic state. -/
def setExtra (allocation : Allocation Prov Extra) (extra : Extra) :
    Allocation Prov Extra :=
  allocation.mapExtra (fun _ => extra)

/-- Attach once at actual backing creation; metadata transformations preserve
this owner. Cloning bytes must allocate a fresh backing before attaching it. -/
def attachNativeBuffer (allocation : Allocation Prov Extra) (owner : NativeBufferOwnership) :
    Except String (Allocation Prov Extra) := do
  if owner.pointer == 0 then throw "cannot attach null native backing"
  if allocation.nativeBuffer.isSome then throw "allocation already owns native backing"
  pure {allocation with nativeBuffer := some owner}

def withoutNativeBuffer (allocation : Allocation Prov Extra) : Allocation Prov Extra :=
  {allocation with nativeBuffer := none}

def len (allocation : Allocation Prov Extra) : Nat := allocation.rawBytes.size

def byteSize (allocation : Allocation Prov Extra) : Size := allocation.size

def provenanceMap (allocation : Allocation Prov Extra) : ProvenanceMap Prov :=
  allocation.provenance

def initializationMask (allocation : Allocation Prov Extra) : InitMask :=
  allocation.initMask

/-- Source `Allocation::adjust_from_tcx`, used when importing interned global
and thread-local allocations into a machine with a different byte backend or
provenance representation. The two callbacks preserve the source's allocation
and pointer-conversion failure boundaries. The source `ptrs()` assertion is
reported explicitly when byte-fragment provenance is present. -/
def adjustFromTcx [PointerProvenance Prov] {CallbackError HookState : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (allocateBytes : Array UInt8 → Align → HookState →
      EStateM.Result CallbackError HookState (Array UInt8))
    (adjustPointer : Pointer CtfeProvenance → HookState →
      EStateM.Result CallbackError HookState (Pointer Prov)) :
    EStateM (AllocationAdjustError CallbackError) HookState (Allocation Prov Unit) :=
  fun initialHookState => Id.run do
    let allocationResult ← match allocateBytes source.rawBytes source.align initialHookState with
      | .ok bytes nextState => pure (bytes, nextState)
      | .error reason nextState => return .error (.byteConversion reason) nextState
    let mut bytes := allocationResult.1
    let mut hookState := allocationResult.2
    if bytes.size != source.rawBytes.size then
      return .error (.allocation (.storageLengthMismatch source.size bytes.size)) hookState
    if source.provenance.byteFragments.isSome then
      return .error (.allocation .allocationHasByteFragmentProvenance) hookState
    let ptrBytes := pointerSize layout
    let mut newProvenance := #[]
    for (offset, sourceProvenance) in source.provenance.ptrs do
      let start := offset.bytes.toNat
      let finish := start + ptrBytes.bytes.toNat
      if finish > bytes.size then
        return .error (.allocation (.invalidSliceEndpoints start finish bytes.size)) hookState
      let pointerBytes := bytes.extract start finish
      let bits ← match readTargetUInt layout pointerBytes with
        | .ok bits => pure bits
        | .error reason => return .error (.allocation reason) hookState
      if bits.toNat > maxU64Nat then
        return .error (.allocation (.pointerBitsDoNotFitOffset bits)) hookState
      let adjusted ← match adjustPointer
          (Pointer.new sourceProvenance (Size.ofBytes (UInt64.ofNat bits.toNat))) hookState with
        | .ok adjusted nextState =>
            hookState := nextState
            pure adjusted
        | .error reason nextState =>
            return .error (.pointerAdjustment reason) nextState
      let encoded ← match targetUIntBytes layout ptrBytes
          (BitVec.ofNat 128 adjusted.offset.bytes.toNat) with
        | .ok encoded => pure encoded
        | .error reason => return .error (.allocation reason) hookState
      bytes := bytes.extract 0 start ++ encoded ++ bytes.extract finish bytes.size
      newProvenance := newProvenance.push (offset, adjusted.provenance)
    let provenance ← match ProvenanceMap.fromPresortedPtrs newProvenance with
      | .ok provenance => pure provenance
      | .error reason =>
          return .error (.allocation (.provenance reason)) hookState
    return .ok ⟨bytes, source.size, provenance, source.initMask, source.align,
      source.mutability, (), none⟩ hookState

private def checkedSlice (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) := do
  if allocation.rawBytes.size != allocation.size.bytes.toNat then
    throw (.storageLengthMismatch allocation.size allocation.rawBytes.size)
  let finish ← range.endExclusive |>.mapError AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.size.bytes then
    throw (.outOfBounds range allocation.size)
  return allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat

/-- Raw bytes with the source method's caller-side bounds precondition made
explicit rather than relying on a host array indexing panic. -/
def getBytesUnchecked (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) :=
  checkedSlice allocation range

/-- Inspect raw bytes outside interpreter execution, including uninitialized
bytes and provenance. The source slice panics for invalid endpoints; Lean
reports that invalid domain explicitly. -/
def inspectWithUninitAndPtrOutsideInterpreter
    (allocation : Allocation Prov Extra) (start finish : Nat) :
    Except AllocError (Array UInt8) := do
  if start > finish || finish > allocation.rawBytes.size then
    throw (.invalidSliceEndpoints start finish allocation.rawBytes.size)
  return allocation.rawBytes.extract start finish

/-- Adopt a snapshot of this allocation's actual native backing storage after
an external host operation. The host must report the very same allocation;
this is not an interpreter write: initialization, provenance, permissions and
extras remain unchanged until source process_native_write/trace processing. -/
def refreshNativeBytes (allocation : Allocation Prov Extra) (bytes : Array UInt8) :
    Except AllocError (Allocation Prov Extra) := do
  unless bytes.size == allocation.size.bytes.toNat do
    throw (.storageLengthMismatch allocation.size bytes.size)
  return {allocation with rawBytes := bytes}

/-- Matches `Allocation::get_bytes_strip_provenance`: check initialization
first, then reject overlapping non-address provenance when required, then
return bytes. `layout` supplies the target pointer width used by the map. -/
def getBytesStripProvenance [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) : Except AllocError (Array UInt8) := do
  match ← (allocation.initMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  if !PointerProvenance.offsetIsAddr (Prov := Prov) then
    let ptrBytes := pointerSize layout
    let isEmpty ← (allocation.provenance.rangeEmpty range ptrBytes).mapError AllocError.provenance
    if !isEmpty then
      let entries ← (allocation.provenance.getRange range ptrBytes).mapError AllocError.provenance
      let some (provRange, _) := entries[0]?
        | throw .nonEmptyProvenanceWithoutEntry
      let provFinish ← provRange.endExclusive |>.mapError AllocError.memory
      let rangeFinish ← range.endExclusive |>.mapError AllocError.memory
      let badStart := if provRange.start.bytes > range.start.bytes
        then provRange.start else range.start
      let badFinish := if provFinish.bytes < rangeFinish.bytes
        then provFinish else rangeFinish
      let bad ← (AllocRange.fromEndpoints badStart badFinish).mapError AllocError.memory
      throw (.readPointerAsInt (some ⟨range, bad⟩))
  checkedSlice allocation range

/-! Scalar memory access. The source assumes caller-side bounds and alignment;
these Lean methods keep invalid ranges as explicit errors instead of array
panics. -/

def readScalar [DecidableEq Prov] [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    Except AllocError (Scalar Prov) := do
  match ← (allocation.initMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← checkedSlice allocation range
  let bits ← readTargetUInt layout bytes
  if readProvenance then
    let targetSize := pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenance.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Scalar.fromPointer layout
        (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
  else
    if PointerProvenance.offsetIsAddr (Prov := Prov) then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    let isEmpty ← (allocation.provenance.rangeEmpty range (pointerSize layout)).mapError AllocError.provenance
    if isEmpty then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

/-- The full source `Allocation::write_scalar` state transition. It checks
mutability, decodes the scalar, marks initialization, clears overwritten
provenance against the old bytes, writes target-endian bits, then inserts a
pointer provenance entry when the value is a pointer. -/
def writeScalar (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar Prov) : EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let bitsAndPointer ← match value.toBitsOrPtrInternal range.size with
    | .ok converted => pure converted
    | .error reason => return .error (.scalar reason) state
  match checkedSlice state range with
  | .error error => return .error error state
  | .ok _ => pure ()
  let nextMask ← match state.initMask.setRange range true with
    | .ok mask => pure mask
    | .error error => return .error (.memory error) state
  let beforeClear := { state with initMask := nextMask }
  match state.provenance.clear range state.rawBytes (pointerSize layout) with
  | .error reason mapAfter =>
    return .error (.provenance reason) { beforeClear with provenance := mapAfter }
  | .ok () clearedMap =>
    let finish := range.start.bytes.toNat + range.size.bytes.toNat
    let start := range.start.bytes.toNat
    let (bits, provenance) := match bitsAndPointer with
      | .bits bits => (bits, none)
      | .pointer pointer => (BitVec.ofNat 128 pointer.offset.bytes.toNat, some pointer.provenance)
    let data ← match targetUIntBytes layout range.size bits with
      | .ok data => pure data
      | .error error => return .error error { beforeClear with provenance := clearedMap }
    let bytes := state.rawBytes.extract 0 start ++ data ++
      state.rawBytes.extract finish state.rawBytes.size
    if bytes.size != state.size.bytes.toNat then
      return .error (.storageLengthMismatch state.size bytes.size)
        { beforeClear with provenance := clearedMap }
    let afterWrite := { beforeClear with rawBytes := bytes, provenance := clearedMap }
    match provenance with
    | none => return .ok () afterWrite
    | some provenance =>
      if range.size != pointerSize layout then
        return .error (.scalarPointerNotTargetSized range.size (pointerSize layout)) afterWrite
      match clearedMap.insertPtr range.start provenance (pointerSize layout) with
      | .error reason mapAfter =>
        return .error (.provenance reason) { afterWrite with provenance := mapAfter }
      | .ok () insertedMap =>
        return .ok () { afterWrite with provenance := insertedMap }

/-- Pointer-valued convenience wrapper around the source scalar write path. -/
def writePointer (layout : TargetDataLayout) (range : AllocRange)
    (pointer : Pointer Prov) : EStateM AllocError (Allocation Prov Extra) Unit :=
  writeScalar layout range (Scalar.fromPointer layout pointer)

private def runProvenanceMutation {α : Type}
    (mutation : EStateM.Result ProvenanceMapError (ProvenanceMap Prov) α)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) α :=
  match mutation with
  | .ok value provenance => .ok value { state with provenance }
  | .error reason provenance => .error (.provenance reason) { state with provenance }

private def setInitialization (state : Allocation Prov Extra) (range : AllocRange)
    (initialized : Bool) : Except AllocError (Allocation Prov Extra) := do
  let initMask ← state.initMask.setRange range initialized |>.mapError AllocError.memory
  return { state with initMask }

private def overwriteRawBytes (state : Allocation Prov Extra) (range : AllocRange)
    (bytes : Array UInt8) : Except AllocError (Allocation Prov Extra) := do
  let finish ← range.endExclusive |>.mapError AllocError.memory
  let start := range.start.bytes.toNat
  let endIndex := finish.bytes.toNat
  let updated := state.rawBytes.extract 0 start ++ bytes ++
    state.rawBytes.extract endIndex state.rawBytes.size
  if updated.size != state.size.bytes.toNat then
    throw (.storageLengthMismatch state.size updated.size)
  return { state with rawBytes := updated }

/-- Source `get_bytes_unchecked_for_overwrite`: mark bytes initialized and
clear any overlapping provenance before the caller writes new bytes. -/
private def prepareForOverwrite (range : AllocRange) (pointerSize : Size)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) Unit := Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenance.clear range initialized.rawBytes pointerSize) initialized

/-- Write a finite byte stream into this allocation. The array length is the
exact iterator length used by `write_bytes_ptr`; the range is derived from
that length, and bounds remain an explicit caller-side check. -/
def writeBytes (start : Size) (bytes : Array UInt8) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let writeSize ← match sizeForArray bytes.size with
    | .ok size => pure size
    | .error reason => return .error reason state
  let range := allocRange start writeSize
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if writeSize.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  let clearedResult := initialized.provenance.clear range initialized.rawBytes pointerSize
  let cleared ← match clearedResult with
    | .ok () provenance => pure { initialized with provenance }
    | .error reason provenance =>
        return .error (.provenance reason) { initialized with provenance }
  match overwriteRawBytes cleared range bytes with
  | .ok updated => return .ok () updated
  | .error reason => return .error reason cleared

/-- Write a repeated byte without materializing an input array. This is the
finite-array counterpart of rustc `write_bytes_ptr` with
`std::iter::repeat_n`: perform the same checked range, mutability,
initialization, and provenance transitions as `writeBytes`, then fill the
already allocated storage in place. -/
def writeRepeatedByte (start : Size) (byte : UInt8) (count : UInt64)
    (pointerSize : Size) : EStateM AllocError (Allocation Prov Extra) Unit :=
  fun state => Id.run do
    let range := allocRange start (Size.ofBytes count)
    match checkedSlice state range with
    | .error reason => return .error reason state
    | .ok _ => pure ()
    if count == 0 then return .ok () state
    if state.mutability != .Mut then return .error .readOnlyAllocation state
    let initialized ← match setInitialization state range true with
      | .ok initialized => pure initialized
      | .error reason => return .error reason state
    let clearedResult := initialized.provenance.clear range initialized.rawBytes pointerSize
    let cleared ← match clearedResult with
      | .ok () provenance => pure { initialized with provenance }
      | .error reason provenance =>
          return .error (.provenance reason) { initialized with provenance }
    let startIndex := start.bytes.toNat
    let mut bytes := cleared.rawBytes
    for offset in [:count.toNat] do
      let index := startIndex + offset
      if h : index < bytes.size then
        bytes := bytes.set index byte h
      else
        return .error (.invalidSliceEndpoints startIndex (index + 1) bytes.size) cleared
    return .ok () { cleared with rawBytes := bytes }

/-- Source `Allocation::write_uninit`: clear initialization first, then clear
overlapping provenance, while leaving the arbitrary byte representation alone. -/
def writeUninit (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let uninitialized ← match setInitialization state range false with
    | .ok uninitialized => pure uninitialized
    | .error reason => return .error reason state
  let cleared := uninitialized.provenance.clear range uninitialized.rawBytes pointerSize
  match cleared with
  | .ok () provenance => return .ok () { uninitialized with provenance }
  | .error reason provenance =>
      return .error (.provenance reason) { uninitialized with provenance }

/-- Source `Allocation::clear_provenance`: preserve bytes and initialization,
but remove or fragment all pointer provenance intersecting the checked range. -/
def clearProvenance (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let cleared := state.provenance.clear range state.rawBytes pointerSize
  match cleared with
  | .ok () provenance => return .ok () { state with provenance }
  | .error reason provenance => return .error (.provenance reason) { state with provenance }

/-- Source `Allocation::process_native_write`: mark the selected range
initialized, then replace provenance in it with wildcard byte fragments. This
is intentionally available only to provenance types with a wildcard. Range
and mutability failures are explicit; a missing wildcard remains an error
after the source-ordered initialization transition. -/
def processNativeWrite [PointerProvenance Prov]
    (layout : TargetDataLayout) (range? : Option AllocRange) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let range := range?.getD (allocRange Size.ZERO state.size)
  if range.size.bytes != 0 then
    match checkedSlice state range with
    | .error _ => return .error (.nativeWriteRangeOutOfBounds range state.size) state
    | .ok _ => pure ()
  if range.size.bytes != 0 && state.mutability != .Mut then
    return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenance.writeWildcards range initialized.rawBytes (pointerSize layout))
    initialized

/-- Source `Allocation::provenance_merge_bytes`: attempt to coalesce complete
byte-fragment pointers. A `false` result may retain successful earlier
coalescings, exactly as the source map iteration does. -/
def provenanceMergeBytes [DecidableEq Prov]
    (layout : TargetDataLayout) :
    EStateM AllocError (Allocation Prov Extra) Bool := fun state => Id.run do
  match state.provenance.mergeBytes (pointerSize layout) with
  | .ok merged provenance => return .ok merged { state with provenance }
  | .error reason provenance => return .error (.provenance reason) { state with provenance }

/-- Source allocation-level half of `mem_copy_repeatedly`. Pointer resolution,
access checks, and machine hooks are supplied by the caller. The source's
initialization and provenance snapshots are prepared before destination
overwrite clears its old metadata. -/
def copyRepeatedly
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (repeatCount : UInt64) (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let sourceBytes ← match checkedSlice source sourceRange with
    | .error reason => return .error reason state
    | .ok sourceBytes => pure sourceBytes
  let totalSize ← match Size.mul sourceRange.size repeatCount with
    | .ok size => pure size
    | .error reason => return .error (.memory (.sizeError reason)) state
  let destRange := allocRange destStart totalSize
  match checkedSlice state destRange with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let provenance ← match source.provenance.prepareCopy sourceRange source.rawBytes pointerSize with
    | .ok copy => pure copy
    | .error reason => return .error (.provenance reason) state
  let initialized ← match source.initMask.prepareCopy sourceRange with
    | .ok copy => pure copy
    | .error reason => return .error (.memory reason) state
  let prepared := prepareForOverwrite destRange pointerSize state
  let afterClear ← match prepared with
    | .ok () updated => pure updated
    | .error reason updated => return .error reason updated
  if initialized.noBytesInit then
    let uninitResult := Allocation.writeUninit destRange pointerSize afterClear
    match uninitResult with
    | .error reason updated => return .error reason updated
    | .ok () updated => return .ok () updated
  if sameAllocation && nonoverlapping then
    let sourceFinish ← match sourceRange.endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    let firstDestFinish ← match (allocRange destStart sourceRange.size).endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    if sourceRange.start.bytes < firstDestFinish.bytes && destStart.bytes < sourceFinish.bytes then
      return .error .copyRangesOverlap afterClear
  if repeatCount > 1 && !nonoverlapping then
    return .error .repeatedCopyRequiresNonoverlapping afterClear
  if sourceRange.size.bytes == 1 && repeatCount == 0 && !initialized.noBytesInit then
    return .error .singleByteZeroCountCopy afterClear
  let mut copiedBytes := #[]
  for _ in [:repeatCount.toNat] do
    copiedBytes := copiedBytes ++ sourceBytes
  let afterBytes ← match overwriteRawBytes afterClear destRange copiedBytes with
    | .ok updated => pure updated
    | .error reason => return .error reason afterClear
  let afterInit ← match afterBytes.initMask.applyCopy initialized
      (allocRange destStart sourceRange.size) repeatCount with
    | .ok initMask => pure { afterBytes with initMask }
    | .error reason => return .error (.memory reason) afterBytes
  match afterInit.provenance.applyCopy provenance
      (allocRange destStart sourceRange.size) repeatCount with
  | .ok () provenance => return .ok () { afterInit with provenance }
  | .error reason provenance =>
      return .error (.provenance reason) { afterInit with provenance }

/-- The source `mem_copy` operation is a one-copy specialization. -/
def copy
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit :=
  copyRepeatedly source sourceRange destStart 1 pointerSize sameAllocation nonoverlapping

/-- Source allocation mutability is a public field. This update preserves
all byte, initialization, provenance and allocation-extra state. -/
def withMutability (self : Allocation Prov Extra) (mutability : Mutability) :
    Allocation Prov Extra :=
  ⟨self.rawBytes, self.size, self.provenance, self.initMask, self.align, mutability, self.extra, self.nativeBuffer⟩

/-- Validated serialization boundary for an interned compiler allocation.
Unlike writes, importing its image does not initialize bytes, clear provenance,
or change the byte representation of pointers. -/
def fromCompilerImage (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (mask : InitMask) (provenance : ProvenanceMap CtfeProvenance) (pointerSize : Size) :
    Except AllocError (Allocation CtfeProvenance Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if mask.len != size then throw (.storageLengthMismatch size mask.len.bytes.toNat)
  for i in [:bytes.size] do
    let _ ← (mask.get (Size.ofBytes (UInt64.ofNat i))).mapError AllocError.memory
  if pointerSize.bytes == 0 then throw (.provenance .pointerSizeZero)
  if provenance.byteFragments.isSome then throw .allocationHasByteFragmentProvenance
  let _ ← (ProvenanceMap.fromPresortedPtrs provenance.ptrs).mapError AllocError.provenance
  let mut previousEnd := 0
  for (offset, _) in provenance.ptrs do
    let start := offset.bytes.toNat
    let finish := start + pointerSize.bytes.toNat
    if start < previousEnd then throw (.provenance .insertOverlapsExistingProvenance)
    if finish > bytes.size then throw (.outOfBounds (allocRange offset pointerSize) size)
    previousEnd := finish
  return ⟨bytes, size, provenance, mask, align, mutability, (), none⟩

end Allocation

end Miri.Memory

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {P E E' : Type}
theorem writeScalar_mapExtra (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar P) (allocation : Allocation P E) (f : E → E') :
    Allocation.writeScalar layout range value (allocation.mapExtra f) =
      (match Allocation.writeScalar layout range value allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : Allocation.getBytesUnchecked (allocation.mapExtra f) range =
      Allocation.getBytesUnchecked allocation range := rfl
  unfold Allocation.getBytesUnchecked at slices
  unfold Allocation.writeScalar
  rw [slices]
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  by_cases mutable : allocation.mutability = .Mut
  · cases converted : value.toBitsOrPtrInternal range.size <;>
      simp_all only [Allocation.mapExtra,mutable,beq_self_eq_true,Bool.not_true,↓reduceIte]
    all_goals repeat' (split <;> try simp_all [Allocation.mapExtra])
  · simp [Allocation.mapExtra,mutable]

theorem writeUninit_mapExtra (range : AllocRange) (pointerSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.writeUninit range pointerSize (allocation.mapExtra f) =
      (match Allocation.writeUninit range pointerSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : Allocation.getBytesUnchecked (allocation.mapExtra f) range =
      Allocation.getBytesUnchecked allocation range := rfl
  unfold Allocation.getBytesUnchecked at slices
  unfold Allocation.writeUninit
  rw [slices]
  unfold setInitialization
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure,Except.mapError,Except.bind]
  cases mask : allocation.initializationMask.setRange range false <;>
    simp only [Allocation.initializationMask] at mask
  all_goals simp only [mask,Except.pure,Allocation.mapExtra]
  all_goals repeat' (split <;> try simp_all [Allocation.mapExtra,Except.pure])


end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {P : Type}

theorem tryNew_uninit_image (size : Size) (align : Align) (pointerSize : Size)
    (allocation : Allocation P Unit) (positive : pointerSize.bytes ≠ 0)
    (created : Allocation.tryNew size align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation) :
    allocation.len = size.bytes.toNat ∧
    ∃ initialized, Allocation.fromBytes (Array.replicate size.bytes.toNat 0) align .Mut = .ok initialized ∧
      Allocation.writeUninit (allocRange Size.ZERO size) pointerSize initialized =
        .ok () (if size.bytes = 0 then {allocation with initMask := InitMask.new size true} else allocation) := by
  unfold Allocation.tryNew at created
  cases checked : checkedAlign align with
  | error error => simp [checked,bind,Bind.bind,Except.bind] at created
  | ok normalized =>
    simp only [checked,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at created
    simp only [Array.size_replicate] at created
    cases nz : firstNonZero (Array.replicate size.bytes.toNat 0) with
    | some pair => cases pair; simp_all [throw,MonadExceptOf.throw,throwThe]
    | none =>
      simp_all
      subst allocation
      refine ⟨by simp [Allocation.len],?_⟩
      refine ⟨⟨Array.replicate size.bytes.toNat 0,size,ProvenanceMap.new,
        InitMask.new size true,normalized,.Mut,(),none⟩,?_,?_⟩
      · have bound : ¬maxU64Nat < size.bytes.toNat := by
          unfold maxU64Nat
          have := size.bytes.toNat_lt
          omega
        have eta : Size.ofBytes size.bytes = size := by cases size; rfl
        unfold Allocation.fromBytes sizeForArray
        simp only [Array.size_replicate,bound,↓reduceIte]
        simp_all [eta,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
      · have endEq : (allocRange Size.ZERO size).endExclusive = .ok size := by
          cases size
          simp [AllocRange.endExclusive,AllocRange.end,allocRange,Size.ZERO,Size.add,Size.ofBytes,Except.mapError]
        unfold Allocation.writeUninit setInitialization checkedSlice
        simp only [Array.size_replicate]
        rw [endEq]
        simp only [bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure,Id.run]
        simp only [allocRange,Size.ZERO,Size.ofBytes]
        simp only [UInt64.not_lt_zero,UInt64.lt_irrefl,↓reduceIte]
        have maskEq := InitMask.full_overwrite_stays_lazy size size true false (allocRange Size.ZERO size)
          endEq rfl (by exact UInt64.le_refl _)
        simp only [allocRange,Size.ZERO,Size.ofBytes] at maskEq
        rw [maskEq]
        by_cases zero : size.bytes = 0
        · simp [zero]
        · simp only [zero,↓reduceIte,Except.bind,Except.mapError,pure,Pure.pure,Except.pure]
          have cleared := ProvenanceMap.clear_new (P := P) (allocRange Size.ZERO size)
            (Array.replicate size.bytes.toNat 0) pointerSize size positive endEq
          simp only [allocRange,Size.ZERO,Size.ofBytes] at cleared
          rw [cleared]
          simp [zero,bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure,Id.run]

end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
private theorem firstNonZero_replicate (n : Nat) : firstNonZero (Array.replicate n 0) = none := by
  let step : Nat → Option (Option (Nat × UInt8)) × Unit → Id (ForInStep (Option (Option (Nat × UInt8)) × Unit)) :=
    fun index _ => match (Array.replicate n 0)[index]? with
      | some byte => if byte != 0 then pure (.done (some (some (index,byte)),())) else pure (.yield (none,()))
      | none => pure (.done (some (some (index,0)),()))
  have scan : ∀ indices : List Nat, (∀ index ∈ indices, index < n) →
      forIn indices (none,()) step = (none,()) := by
    intro indices
    induction indices with
    | nil => intro good; rfl
    | cons head tail ih =>
      intro good
      have bound := good head (by simp)
      have atHead : (Array.replicate n (0 : UInt8))[head]? = some 0 := by simp [bound]
      rw [List.forIn_cons]
      simp only [step,atHead,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        pure,Pure.pure,bind,Bind.bind]
      exact ih (by intro index member; exact good index (by simp [member]))
  simp only [firstNonZero]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Array.size_replicate,Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  dsimp only [step,Id.run,pure,Pure.pure] at scan
  rw [scan (List.range' 0 n) (by intro index member; have := List.mem_range'.mp member; omega)]
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P : Type}

theorem tryNew_replicate (size : Size) (align : Align) (alignmentBytes : UInt64)
    (bytes : Align.bytes align = .ok alignmentBytes)
    (normalized : Align.fromBytes alignmentBytes = .ok align) :
    ∃ allocation : Allocation P Unit,
      Allocation.tryNew size align .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation ∧
      allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
      allocation.nativeBuffer = none ∧ allocation.mutability = .Mut := by
  refine ⟨⟨Array.replicate size.bytes.toNat 0,size,ProvenanceMap.new,
    InitMask.new size false,align,.Mut,(),none⟩,?_,rfl,by simp [Allocation.len],rfl,rfl⟩
  simp [Allocation.tryNew,checkedAlign,bytes,normalized,firstNonZero_replicate,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.mapError]

end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P : Type}

theorem tryNew_replicate_full (size : Size) (align : Align) (alignmentBytes : UInt64)
    (bytes : Align.bytes align = .ok alignmentBytes)
    (normalized : Align.fromBytes alignmentBytes = .ok align) :
    ∃ allocation : Allocation P Unit,
      Allocation.tryNew size align .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation ∧
      allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
      allocation.nativeBuffer = none ∧ allocation.mutability = .Mut ∧ allocation.align = align := by
  refine ⟨⟨Array.replicate size.bytes.toNat 0,size,ProvenanceMap.new,
    InitMask.new size false,align,.Mut,(),none⟩,?_,rfl,by simp [Allocation.len],rfl,rfl,rfl⟩
  simp [Allocation.tryNew,checkedAlign,bytes,normalized,firstNonZero_replicate,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.mapError]

end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem target_bytes_exists (layout : TargetDataLayout) (size : Size) (bits : U128)
    (limit : size.bytes.toNat ≤ 16) :
    ∃ bytes, targetUIntBytes layout size bits = .ok bytes ∧ bytes.size = size.bytes.toNat := by
  let step : Nat → Array UInt8 → Except AllocError (ForInStep (Array UInt8)) := fun index bytes =>
    let valueIndex := if layout.endian == .little then index else size.bytes.toNat-index-1
    pure (.yield (bytes.push (UInt8.ofNat ((bits.toNat / 2^(8*valueIndex)) % 256))))
  have build : ∀ (indices : List Nat) (initial : Array UInt8),
      ∃ bytes, forIn indices initial step = .ok bytes ∧ bytes.size = initial.size+indices.length := by
    intro indices
    induction indices with
    | nil => intro initial; exact ⟨initial,rfl,by simp⟩
    | cons index rest ih =>
      intro initial
      let byte := UInt8.ofNat ((bits.toNat / 2^(8*(if layout.endian == .little then index else size.bytes.toNat-index-1))) % 256)
      obtain ⟨bytes,ok,length⟩ := ih (initial.push byte)
      refine ⟨bytes,?_,?_⟩
      · simpa only [List.forIn_cons,step,byte,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] using ok
      · simp_all [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have small : ¬size.bytes > 16 := by
    simp only [UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr limit
  unfold targetUIntBytes
  simp only [small,↓reduceIte,Std.Legacy.Range.forIn_eq_forIn_range']
  obtain ⟨bytes,ok,length⟩ := build (List.range' 0 [:size.bytes.toNat].size) #[]
  refine ⟨bytes,?_,?_⟩
  · dsimp only [step] at ok
    rw [ok]
    rfl
  · simpa using length
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
variable {P E : Type}
private theorem write_add_size (left right : Size)
    (fits : left.bytes.toNat+right.bytes.toNat < 2^64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes+right.bytes)) := by
  have noWrap : ¬left.bytes+right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt,UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    omega
  simp [Size.add,noWrap]

private theorem scalar_with_transitions (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0) (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat+range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : allocation.provenanceMap.clear range allocation.rawBytes (pointerSize layout) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = pointerSize layout ∧
          cleared.insertPtr range.start pointer.provenance (pointerSize layout) = .ok () nextProvenance) :
    ∃ updated, Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧ updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧ updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧ updated.provenanceMap = nextProvenance := by
  have fits : range.start.bytes.toNat+range.size.bytes.toNat < 2^64 := by
    have := allocation.byteSize.bytes.toNat_lt
    omega
  let finish := Size.ofBytes (range.start.bytes+range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat+range.size.bytes.toNat := by
    simp only [finish,Size.ofBytes,UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  obtain ⟨mask,maskOk,maskSize,maskWF⟩ := InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
    maskValid endpoint (by omega) (by rw [maskLength]; simpa only [finishNat] using bound)
  let bits := match converted with
    | .bits bits => bits
    | .pointer pointer => BitVec.ofNat 128 pointer.offset.bytes.toNat
  obtain ⟨data,dataOk,dataSize⟩ := target_bytes_exists layout range.size bits width
  let bytes := allocation.rawBytes.extract 0 range.start.bytes.toNat ++ data ++
    allocation.rawBytes.extract (range.start.bytes.toNat+range.size.bytes.toNat) allocation.rawBytes.size
  have startBound : range.start.bytes.toNat ≤ allocation.rawBytes.size := by
    change range.start.bytes.toNat ≤ allocation.len
    omega
  have endBound : finish.bytes.toNat ≤ allocation.rawBytes.size := by
    change finish.bytes.toNat ≤ allocation.len
    omega
  have bytesLength : bytes.size = allocation.byteSize.bytes.toNat := by
    simp only [bytes,Array.size_append,Array.size_extract,Nat.min_eq_left startBound,Nat.min_self,
      Nat.sub_zero,dataSize,Nat.min_eq_left (by omega : range.start.bytes.toNat+range.size.bytes.toNat ≤ allocation.rawBytes.size)]
    change _ = allocation.byteSize.bytes.toNat
    change allocation.rawBytes.size = allocation.byteSize.bytes.toNat at storage
    omega
  let updated : Allocation P E :=
    ⟨bytes,allocation.byteSize,nextProvenance,mask,allocation.align,allocation.mutability,allocation.extra,allocation.nativeBuffer⟩
  refine ⟨updated,?_,rfl,?_,rfl,rfl,rfl,rfl,maskSize,maskWF,rfl⟩
  · have slice : checkedSlice allocation range = .ok (allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
      unfold checkedSlice
      change allocation.rawBytes.size = allocation.size.bytes.toNat at storage
      simp [storage,endpoint,finishNat,UInt64.lt_iff_toNat_lt,bound,bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure]
      exact bound
    simp only [Allocation.initializationMask] at maskOk
    simp only [Allocation.provenanceMap] at clear
    unfold Allocation.writeScalar
    simp only [mutable,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,conversion]
    simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
    rw [slice,maskOk]
    simp only [bind,Bind.bind,pure,Pure.pure]
    rw [clear]
    simp only [bind,Bind.bind,pure,Pure.pure]
    dsimp only [bytes,Allocation.byteSize] at bytesLength
    cases converted with
    | bits payload =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      simp [insert,updated,bytes,mutable,bind,Bind.bind,pure,Pure.pure]
      rfl
    | pointer pointer =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      rcases insert with ⟨sizeEq,inserted⟩
      simp only [sizeEq,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      rw [inserted]
      simp [updated,bytes,mutable,sizeEq]
      rfl
  · change bytes.size = allocation.len
    exact bytesLength.trans storage.symm
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
variable {P E : Type}
private def zeroPointer (provenance : P) : ProvenanceMap P :=
  match ProvenanceMap.insertPtr Size.ZERO provenance (Size.ofBytes 8) ProvenanceMap.new with
  | .ok _ state => state
  | .error _ state => state

/-- Successful physical first component write in fresh uninitialized storage.
All non-byte metadata is retained; only an optional zero-offset pointer entry
can be present for the subsequent disjoint component. -/
theorem writeScalar_fresh_zero (layout : TargetDataLayout) (allocation : Allocation P E) (value : Scalar P)
    (converted : ScalarBitsOrPointer P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (empty : allocation.provenanceMap = ProvenanceMap.new)
    (nonzero : value.size.bytes ≠ 0) (width : value.size.bytes.toNat ≤ 16)
    (bound : value.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (target : layout.pointerWidth = .w64)
    (pointerWidth : match converted with | .bits _ => True | .pointer _ => value.size = Size.fromBits layout.pointerWidth.bits)
    (conversion : value.toBitsOrPtrInternal value.size = .ok converted) :
    ∃ updated, Allocation.writeScalar layout (allocRange Size.ZERO value.size) value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧ updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧ updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      (updated.provenanceMap = ProvenanceMap.new ∨
        value.size = pointerSize layout ∧ ∃ provenance, updated.provenanceMap = zeroPointer provenance) := by
  have pointerDef : pointerSize layout = Size.fromBits layout.pointerWidth.bits := rfl
  simp only [←pointerDef] at pointerWidth
  have positive : (pointerSize layout).bytes ≠ 0 := by simp [pointerSize,target,PointerWidth.bits,Size.fromBits,Size.ofBytes]
  have endpoint : (allocRange Size.ZERO value.size).endExclusive = .ok value.size := by
    cases sized : value.size
    simp [allocRange,AllocRange.endExclusive,AllocRange.end,Size.ZERO,Size.ofBytes,Size.add,Except.mapError]
  have clear : allocation.provenanceMap.clear (allocRange Size.ZERO value.size) allocation.rawBytes (pointerSize layout) =
      .ok () ProvenanceMap.new := by
    rw [empty]
    exact ProvenanceMap.clear_new _ _ _ _ positive endpoint
  cases converted with
  | bits bits =>
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,provenance⟩ :=
      scalar_with_transitions layout allocation (allocRange Size.ZERO value.size) value (.bits bits)
        ProvenanceMap.new ProvenanceMap.new storage mutable maskLength maskValid nonzero width
        (by simpa [allocRange,Size.ZERO,Size.ofBytes] using bound) conversion clear rfl
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,Or.inl provenance⟩
  | pointer pointer =>
    have inserted : ProvenanceMap.insertPtr Size.ZERO pointer.provenance (pointerSize layout) ProvenanceMap.new =
        .ok () (zeroPointer pointer.provenance) := by
      have ptr8 : pointerSize layout = Size.ofBytes 8 := by simp [pointerSize,target,PointerWidth.bits,Size.fromBits]
      have actual := ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8) pointer.provenance
        (by decide) (by decide)
      unfold zeroPointer
      rw [ptr8,actual]
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,provenance⟩ :=
      scalar_with_transitions layout allocation (allocRange Size.ZERO value.size) value (.pointer pointer)
        ProvenanceMap.new (zeroPointer pointer.provenance) storage mutable maskLength maskValid nonzero width
        (by simpa [allocRange,Size.ZERO,Size.ofBytes] using bound) conversion clear ⟨pointerWidth,inserted⟩
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,
      Or.inr ⟨pointerWidth,pointer.provenance,provenance⟩⟩
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
variable {P E : Type}
/-- The second component writes a disjoint window of fresh storage. It keeps
an earlier pointer entry intact and derives every provenance operation. -/
theorem writeScalar_separated (layout : TargetDataLayout) (allocation : Allocation P E) (offset : Size)
    (value : Scalar P) (converted : ScalarBitsOrPointer P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (separated : allocation.provenanceMap = ProvenanceMap.new ∨
      ∃ provenance, allocation.provenanceMap = zeroPointer provenance ∧
        (pointerSize layout).bytes.toNat ≤ offset.bytes.toNat)
    (nonzero : value.size.bytes ≠ 0) (width : value.size.bytes.toNat ≤ 16)
    (bound : offset.bytes.toNat+value.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (target : layout.pointerWidth = .w64)
    (pointerWidth : match converted with | .bits _ => True | .pointer _ => value.size = Size.fromBits layout.pointerWidth.bits)
    (conversion : value.toBitsOrPtrInternal value.size = .ok converted) :
    ∃ updated, Allocation.writeScalar layout (allocRange offset value.size) value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧ updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧ updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask := by
  have pointerDef : pointerSize layout = Size.fromBits layout.pointerWidth.bits := rfl
  simp only [←pointerDef] at pointerWidth
  let range := allocRange offset value.size
  have fits : offset.bytes.toNat+value.size.bytes.toNat < 2^64 := by have := allocation.byteSize.bytes.toNat_lt; omega
  let finish := Size.ofBytes (offset.bytes+value.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end range allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size offset value.size fits)
  have ptr8 : pointerSize layout = Size.ofBytes 8 := by simp [pointerSize,target,PointerWidth.bits,Size.fromBits]
  have positive : (pointerSize layout).bytes ≠ 0 := by rw [ptr8]; decide
  have clear : allocation.provenanceMap.clear range allocation.rawBytes (pointerSize layout) =
      .ok () allocation.provenanceMap := by
    rcases separated with empty | ⟨old,present,before⟩
    · rw [empty]; exact ProvenanceMap.clear_new _ _ _ _ positive endpoint
    · have initial := ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8) old
        (by decide) (by decide)
      unfold zeroPointer at present
      rw [initial] at present
      dsimp only at present
      rw [present]
      exact ProvenanceMap.clear_singleton_before range allocation.rawBytes (pointerSize layout) finish old
        positive before endpoint
  cases converted with
  | bits bits =>
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,_⟩ :=
      scalar_with_transitions layout allocation range value (.bits bits) allocation.provenanceMap allocation.provenanceMap
        storage mutable maskLength maskValid nonzero width bound conversion clear rfl
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid⟩
  | pointer pointer =>
    have insertExists : ∃ next, allocation.provenanceMap.insertPtr offset pointer.provenance (pointerSize layout) =
        .ok () next := by
      rcases separated with empty | ⟨old,present,before⟩
      · rw [empty]
        have actual := ProvenanceMap.insertPtr_new offset (pointerSize layout) finish pointer.provenance positive
          (by simpa only [range,pointerWidth] using endpoint)
        let next := match ProvenanceMap.insertPtr offset pointer.provenance (pointerSize layout) ProvenanceMap.new with
          | .ok _ state => state | .error _ state => state
        refine ⟨next,?_⟩
        dsimp only [next]
        rw [actual]
      · have initial := ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8) old
          (by decide) (by decide)
        unfold zeroPointer at present
        rw [initial] at present
        dsimp only at present
        rw [present]
        exact ProvenanceMap.insertPtr_singleton_after offset (pointerSize layout) finish old pointer.provenance
          positive before (by simpa only [range,pointerWidth] using endpoint)
    obtain ⟨next,inserted⟩ := insertExists
    obtain ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid,_⟩ :=
      scalar_with_transitions layout allocation range value (.pointer pointer) allocation.provenanceMap next
        storage mutable maskLength maskValid nonzero width bound conversion clear ⟨pointerWidth,inserted⟩
    exact ⟨updated,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,maskEq,valid⟩
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P : Type}
theorem tryNew_uninit_shape (size : Size) (align : Align) (allocation : Allocation P Unit)
    (created : Allocation.tryNew size align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation) :
    allocation.provenanceMap = ProvenanceMap.new ∧ allocation.initializationMask = InitMask.new size false := by
  unfold tryNew at created
  cases checked : checkedAlign align with
  | error error => simp [checked,bind,Bind.bind,Except.bind] at created
  | ok normalized =>
    simp [checked,firstNonZero_replicate,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at created
    subst allocation
    exact ⟨rfl,rfl⟩
end Miri.Memory.Allocation

namespace Miri.Memory.Allocation
open Miri.ABI
set_option autoImplicit false
variable {P E E' : Type}

private theorem if_pos_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem if_neg_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : ¬c) :
    (if c then t else e) = e := by
  split
  · next hp => exact absurd hp h
  · rfl

private theorem checkedSlice_ok (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    checkedSlice allocation range =
      .ok (allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  unfold checkedSlice
  change allocation.rawBytes.size = allocation.size.bytes.toNat at storage
  have h_not_s : ¬(finish.bytes < range.start.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr startLe)
  have h_not_f : ¬(allocation.size.bytes < finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr inBounds)
  simp [storage, endEq, h_not_s, h_not_f, bind, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure]

private theorem full_range_endExclusive (sz : Size) :
    (allocRange Size.ZERO sz).endExclusive = .ok sz := by
  cases sz
  simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]

private theorem eq_of_not_bne {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : ¬((a != b) = true)) : a = b := by
  simp [bne] at h
  exact h

private theorem getBytesUnchecked_full_rawBytes (allocation : Allocation P E)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) :
    allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok allocation.rawBytes := by
  unfold Allocation.getBytesUnchecked
  rw [checkedSlice_ok allocation (allocRange Size.ZERO allocation.byteSize) allocation.byteSize
    storage (full_range_endExclusive allocation.byteSize) (Nat.zero_le _) (Nat.le_refl _)]
  dsimp only [allocRange]
  have h_zero : Size.ZERO.bytes.toNat = 0 := rfl
  rw [h_zero, ← storage]
  exact congrArg Except.ok (Array.extract_size (xs := allocation.rawBytes))

private theorem extract_ByteAt (arr : Array UInt8) (start finish idx : Nat)
    (h_fin : finish ≤ arr.size) (h_lo : start ≤ idx) (h_hi : idx < finish) :
    (arr.extract start finish)[idx - start]? = arr[idx]? := by
  have h_idx_lt : idx < arr.size := by omega
  have h_ext_sz : (arr.extract start finish).size = finish - start := by
    simp [Array.size_extract, Nat.min_eq_left h_fin]
  have h_sub_lt : idx - start < (arr.extract start finish).size := by omega
  rw [Array.getElem?_eq_getElem h_sub_lt, Array.getElem?_eq_getElem h_idx_lt, Array.getElem_extract]
  have h_add_sub : start + (idx - start) = idx := by omega
  simp [h_add_sub]

private theorem splice_getElem? (raw data : Array UInt8) (start finish k : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size)[k]? =
      if start ≤ k ∧ k < finish then data[k - start]? else raw[k]? := by
  let pfx := raw.extract 0 start
  let sfx := raw.extract finish raw.size
  have h_pfx_sz : pfx.size = start := by
    simp [pfx, Array.size_extract, Nat.min_eq_left (by omega : start ≤ raw.size)]
  have h_sfx_sz : sfx.size = raw.size - finish := by
    simp [sfx, Array.size_extract]
  by_cases h_lt_start : k < start
  · have h_not_in : ¬(start ≤ k ∧ k < finish) := by omega
    rw [if_neg_eq h_not_in]
    have h1 : (pfx ++ data ++ sfx)[k]? = (pfx ++ data)[k]? :=
      Array.getElem?_append_left (by simp [Array.size_append, h_pfx_sz]; omega)
    have h2 : (pfx ++ data)[k]? = pfx[k]? :=
      Array.getElem?_append_left (by simp [h_pfx_sz, h_lt_start])
    rw [h1, h2]
    have he := extract_ByteAt raw 0 start k (by omega) (Nat.zero_le _) h_lt_start
    simpa [pfx] using he
  · by_cases h_lt_fin : k < finish
    · have h_in : start ≤ k ∧ k < finish := ⟨by omega, h_lt_fin⟩
      rw [if_pos_eq h_in]
      have h1 : (pfx ++ data ++ sfx)[k]? = (pfx ++ data)[k]? :=
        Array.getElem?_append_left (by simp [Array.size_append, h_pfx_sz, h_data_sz]; omega)
      have h2 : (pfx ++ data)[k]? = data[k - pfx.size]? :=
        Array.getElem?_append_right (by simp [h_pfx_sz]; omega)
      simpa [h_pfx_sz] using h1.trans h2
    · have h_not_in : ¬(start ≤ k ∧ k < finish) := by omega
      rw [if_neg_eq h_not_in]
      have h1 : (pfx ++ data ++ sfx)[k]? = sfx[k - (pfx ++ data).size]? :=
        Array.getElem?_append_right (by simp [Array.size_append, h_pfx_sz, h_data_sz]; omega)
      have h_pd_sz : (pfx ++ data).size = finish := by
        simp [Array.size_append, h_pfx_sz, h_data_sz]; omega
      rw [h1, h_pd_sz]
      by_cases h_lt_raw : k < raw.size
      · have he := extract_ByteAt raw finish raw.size k (Nat.le_refl _) (by omega) h_lt_raw
        simpa [sfx] using he
      · have h_none1 : sfx[k - finish]? = none :=
          Array.getElem?_eq_none (by rw [h_sfx_sz]; omega)
        have h_none2 : raw[k]? = none :=
          Array.getElem?_eq_none (by omega)
        exact h_none1.trans h_none2.symm

private theorem splice_extract_exact (raw data : Array UInt8) (start finish : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size).extract start finish = data := by
  let spliced := raw.extract 0 start ++ data ++ raw.extract finish raw.size
  have h_sp_sz : spliced.size = raw.size := by
    simp [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : start ≤ raw.size), h_data_sz]
    omega
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Nat.min_eq_left h_fin, h_data_sz]
  · intro i hi1 hi2
    have hi_lt : i < finish - start := by simpa [h_data_sz] using hi2
    have h_eq? := extract_ByteAt spliced start finish (start + i) (by rw [h_sp_sz]; exact h_fin)
      (by omega) (by omega)
    have h_sub : start + i - start = i := by omega
    rw [h_sub] at h_eq?
    have h_sp_i := splice_getElem? raw data start finish (start + i) h_lo h_fin h_data_sz
    rw [if_pos_eq ⟨by omega, by omega⟩, h_sub] at h_sp_i
    have h_lhs : (spliced.extract start finish)[i]? = some ((spliced.extract start finish)[i]'hi1) :=
      Array.getElem?_eq_getElem hi1
    have h_rhs : data[i]? = some (data[i]'hi2) := Array.getElem?_eq_getElem hi2
    have h_comb : (spliced.extract start finish)[i]? = data[i]? := h_eq?.trans h_sp_i
    exact Option.some.inj (h_lhs.symm.trans (h_comb.trans h_rhs))

private theorem splice_extract_disjoint (raw data : Array UInt8) (wStart wFin qStart qFin : Nat)
    (h_w_lo : wStart ≤ wFin) (h_w_fin : wFin ≤ raw.size)
    (h_q_lo : qStart ≤ qFin) (h_q_fin : qFin ≤ raw.size)
    (h_data_sz : data.size = wFin - wStart)
    (h_disj : wFin ≤ qStart ∨ qFin ≤ wStart) :
    (raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size).extract qStart qFin =
      raw.extract qStart qFin := by
  let spliced := raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size
  have h_sp_sz : spliced.size = raw.size := by
    simp [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ raw.size), h_data_sz]
    omega
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Array.size_extract]
  · intro i hi1 hi2
    have hi_lt : i < qFin - qStart := by
      rw [Array.size_extract, Nat.min_eq_left h_q_fin] at hi2
      exact hi2
    have h_sub : qStart + i - qStart = i := by omega
    have h_eq1 := extract_ByteAt spliced qStart qFin (qStart + i) (by rw [h_sp_sz]; exact h_q_fin)
      (by omega) (by omega)
    have h_eq2 := extract_ByteAt raw qStart qFin (qStart + i) h_q_fin (by omega) (by omega)
    have h_sp_i := splice_getElem? raw data wStart wFin (qStart + i) h_w_lo h_w_fin h_data_sz
    have h_out : ¬(wStart ≤ qStart + i ∧ qStart + i < wFin) := by omega
    rw [if_neg_eq h_out] at h_sp_i
    have h_comb : (spliced.extract qStart qFin)[i]? = (raw.extract qStart qFin)[i]? := by
      simpa [h_sub] using (h_eq1.trans h_sp_i).trans h_eq2.symm
    have h_lhs := Array.getElem?_eq_getElem hi1
    have h_rhs := Array.getElem?_eq_getElem hi2
    exact Option.some.inj (h_lhs.symm.trans (h_comb.trans h_rhs))

theorem byteSize_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).byteSize = allocation.byteSize := rfl

theorem len_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).len = allocation.len := rfl

theorem align_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).align = allocation.align := rfl

theorem mutability_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).mutability = allocation.mutability := rfl

theorem provenanceMap_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).provenanceMap = allocation.provenanceMap := rfl

theorem initializationMask_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).initializationMask = allocation.initializationMask := rfl

theorem getBytesUnchecked_withExtra (allocation : Allocation P Unit) (extra : E) (range : AllocRange) :
    (allocation.withExtra extra).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

theorem byteSize_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).byteSize = allocation.byteSize := rfl

theorem len_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).len = allocation.len := rfl

theorem align_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).align = allocation.align := rfl

theorem mutability_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).mutability = allocation.mutability := rfl

theorem provenanceMap_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).provenanceMap = allocation.provenanceMap := rfl

theorem initializationMask_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).initializationMask = allocation.initializationMask := rfl

theorem getBytesUnchecked_mapExtra (allocation : Allocation P E) (f : E → E') (range : AllocRange) :
    (allocation.mapExtra f).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

theorem getBytesStripProvenance_mapExtra [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout) (range : AllocRange) :
    (allocation.mapExtra f).getBytesStripProvenance layout range =
      allocation.getBytesStripProvenance layout range := rfl

theorem readScalar_mapExtra [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    (allocation.mapExtra f).readScalar layout range readProvenance =
      allocation.readScalar layout range readProvenance := rfl

theorem writeBytes_mapExtra (start : Size) (bytes : Array UInt8) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.writeBytes start bytes ptrSize (allocation.mapExtra f) =
      (match Allocation.writeBytes start bytes ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : ∀ r, checkedSlice (allocation.mapExtra f) r = checkedSlice allocation r := fun _ => rfl
  unfold Allocation.writeBytes setInitialization overwriteRawBytes
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.mapError, slices]
  cases sizeForArray bytes.size with
  | error e => rfl
  | ok writeSize =>
    dsimp only
    cases checkedSlice allocation (allocRange start writeSize) with
    | error e => rfl
    | ok _ =>
      dsimp only
      by_cases h0 : writeSize.bytes == 0
      · simp [h0]
      · simp only [h0, Bool.false_eq_true, ↓reduceIte, Allocation.mapExtra]
        by_cases hm : allocation.mutability != .Mut
        · simp [hm]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte]
          cases allocation.initMask.setRange (allocRange start writeSize) true with
          | error e => simp
          | ok mask =>
            simp only [Except.pure]
            cases allocation.provenance.clear (allocRange start writeSize) allocation.rawBytes ptrSize with
            | error e pm => rfl
            | ok _ pm =>
              dsimp only
              cases (allocRange start writeSize).endExclusive with
              | error e => simp
              | ok fin =>
                dsimp only [Allocation.mapExtra, Except.mapError, Except.bind, Except.pure]
                cases h_len :
                    ((allocation.rawBytes.extract 0 (allocRange start writeSize).start.bytes.toNat ++
                      bytes ++ allocation.rawBytes.extract fin.bytes.toNat).size !=
                      allocation.size.bytes.toNat) <;>
                  simp only [Bool.false_eq_true, ↓reduceIte,
                    throw, MonadExceptOf.throw, throwThe] <;>
                  rfl

theorem clearProvenance_mapExtra (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.clearProvenance range ptrSize (allocation.mapExtra f) =
      (match Allocation.clearProvenance range ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) := by
  have slices : checkedSlice (allocation.mapExtra f) range = checkedSlice allocation range := rfl
  unfold Allocation.clearProvenance
  rw [slices]
  simp only [Id.run, pure, Pure.pure, Allocation.mapExtra]
  cases checkedSlice allocation range with
  | error _ => rfl
  | ok _ =>
    dsimp only
    cases allocation.provenance.clear range allocation.rawBytes ptrSize <;> rfl

private theorem replicate_extract_zero (n start finish : Nat)
    (_h_lo : start ≤ finish) (h_fin : finish ≤ n) :
    (Array.replicate n (0 : UInt8)).extract start finish = Array.replicate (finish - start) 0 := by
  apply Array.ext
  · simp [Array.size_replicate, Nat.min_eq_left h_fin]
  · intro i hi1 hi2
    rw [Array.getElem_extract, Array.getElem_replicate, Array.getElem_replicate]

theorem fromBytes_spec (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (alloc : Allocation P Unit)
    (created : Allocation.fromBytes bytes align mutability = .ok alloc) :
    alloc.byteSize.bytes.toNat = bytes.size ∧
      alloc.len = bytes.size ∧
      alloc.mutability = mutability ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new alloc.byteSize true ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ bytes.size →
        alloc.getBytesUnchecked range =
          .ok (bytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  unfold Allocation.fromBytes at created
  cases h_al : checkedAlign align with
  | error e => simp [h_al, bind, Bind.bind, Except.bind] at created
  | ok normAlign =>
    simp only [h_al, bind, Bind.bind, Except.bind] at created
    cases h_sz : sizeForArray bytes.size with
    | error e => simp [h_sz] at created
    | ok sz =>
      simp only [h_sz] at created
      by_cases h_eq : bytes.size = sz.bytes.toNat
      · simp only [h_eq, ↓reduceDIte, pure, Pure.pure, Except.pure, Except.ok.injEq] at created
        subst created
        refine ⟨h_eq.symm, rfl, rfl, rfl, rfl, rfl, rfl, trivial, ?_⟩
        intro range finish h_end h_lo h_fin
        exact checkedSlice_ok _ range finish h_eq h_end h_lo
          (by dsimp only [Allocation.byteSize]; omega)
      · simp [h_eq] at created

theorem fromBytes_exists (bytes : Array UInt8) (align : Align) (alignmentBytes : UInt64)
    (mutability : Mutability)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align)
    (h_fits : bytes.size < 2 ^ 64) :
    ∃ alloc : Allocation P Unit,
      Allocation.fromBytes bytes align mutability = .ok alloc ∧
      alloc.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      alloc.align = align := by
  have h_ca : checkedAlign align = .ok align := by
    unfold checkedAlign
    simp [h_bytes, h_norm, bind, Bind.bind, Except.bind, Except.mapError, pure, Pure.pure, Except.pure]
  have h_not_gt : ¬(bytes.size > maxU64Nat) := by
    unfold maxU64Nat; omega
  have h_tonat : (Size.ofBytes (UInt64.ofNat bytes.size)).bytes.toNat = bytes.size := by
    simp [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_fits]
  have h_sfa : sizeForArray bytes.size = .ok (Size.ofBytes (UInt64.ofNat bytes.size)) := by
    unfold sizeForArray
    simp [h_not_gt, h_tonat, pure, Pure.pure, Except.pure]
  refine ⟨⟨bytes, Size.ofBytes (UInt64.ofNat bytes.size), ProvenanceMap.new,
    InitMask.new (Size.ofBytes (UInt64.ofNat bytes.size)) true, align, mutability, (), none⟩,
    ?_, rfl, rfl⟩
  unfold Allocation.fromBytes
  simp [h_ca, h_sfa, h_tonat, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

theorem tryNew_spec (size : Size) (align : Align) (init : AllocInit)
    (alloc : Allocation P Unit)
    (created : Allocation.tryNew size align init
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc) :
    alloc.byteSize = size ∧
      alloc.len = size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      (init = .Uninit → alloc.initializationMask = InitMask.new size false) ∧
      (init = .Zero → alloc.initializationMask = InitMask.new size true) ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ size.bytes.toNat →
        alloc.getBytesUnchecked range =
          .ok (Array.replicate (finish.bytes.toNat - range.start.bytes.toNat) 0) := by
  unfold Allocation.tryNew at created
  cases h_al : checkedAlign align with
  | error e => simp [h_al, bind, Bind.bind, Except.bind] at created
  | ok normAlign =>
    let bInit := match init with | .Uninit => false | .Zero => true
    simp [h_al, firstNonZero_replicate,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at created
    subst created
    refine ⟨rfl, Array.size_replicate, rfl, rfl, rfl, rfl,
      fun h => by subst h; rfl, fun h => by subst h; rfl, trivial, ?_⟩
    intro range finish h_end h_lo h_fin
    let a0 : Allocation P Unit :=
      ⟨Array.replicate size.bytes.toNat 0, size, ProvenanceMap.new,
        InitMask.new size bInit, normAlign, .Mut, (), none⟩
    unfold Allocation.getBytesUnchecked
    rw [checkedSlice_ok a0 range finish Array.size_replicate h_end h_lo h_fin]
    exact congrArg Except.ok (replicate_extract_zero size.bytes.toNat _ _ h_lo h_fin)

theorem tryNew_exists (size : Size) (align : Align) (alignmentBytes : UInt64) (init : AllocInit)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align) :
    ∃ alloc : Allocation P Unit,
      Allocation.tryNew size align init
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      alloc.align = align := by
  refine ⟨⟨Array.replicate size.bytes.toNat 0, size, ProvenanceMap.new,
    InitMask.new size (match init with | .Uninit => false | .Zero => true), align, .Mut, (), none⟩,
    ?_, rfl⟩
  simp [Allocation.tryNew, checkedAlign, h_bytes, h_norm, firstNonZero_replicate,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

theorem getBytesUnchecked_size (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ slice, allocation.getBytesUnchecked range = .ok slice ∧
      slice.size = finish.bytes.toNat - range.start.bytes.toNat := by
  refine ⟨allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat,
    checkedSlice_ok allocation range finish storage endEq startLe inBounds, ?_⟩
  change _ = _
  have h_fin_raw : finish.bytes.toNat ≤ allocation.rawBytes.size := by
    change finish.bytes.toNat ≤ allocation.len; omega
  simp [Array.size_extract, Nat.min_eq_left h_fin_raw]

theorem getBytesUnchecked_subrange (allocation : Allocation P E)
    (rOuter rInner : AllocRange) (fOuter fInner : Size) (outerBytes : Array UInt8)
    (h_outer_end : rOuter.endExclusive = .ok fOuter)
    (h_inner_end : rInner.endExclusive = .ok fInner)
    (h_lo : rOuter.start.bytes.toNat ≤ rInner.start.bytes.toNat)
    (h_mid : rInner.start.bytes.toNat ≤ fInner.bytes.toNat)
    (h_hi : fInner.bytes.toNat ≤ fOuter.bytes.toNat)
    (h_outer : allocation.getBytesUnchecked rOuter = .ok outerBytes) :
    allocation.getBytesUnchecked rInner =
      .ok (outerBytes.extract
        (rInner.start.bytes.toNat - rOuter.start.bytes.toNat)
        (fInner.bytes.toNat - rOuter.start.bytes.toNat)) := by
  unfold Allocation.getBytesUnchecked checkedSlice at h_outer
  by_cases h_mis : allocation.rawBytes.size != allocation.size.bytes.toNat
  · simp [h_mis, bind, Bind.bind, Except.bind] at h_outer
  · have h_raw_sz : allocation.rawBytes.size = allocation.size.bytes.toNat := eq_of_not_bne h_mis
    have storage : allocation.len = allocation.byteSize.bytes.toNat := h_raw_sz
    simp only [h_mis, Bool.false_eq_true, ↓reduceIte, h_outer_end, Except.mapError,
      bind, Bind.bind, Except.bind] at h_outer
    by_cases h_oob : rOuter.start.bytes > fOuter.bytes || fOuter.bytes > allocation.size.bytes
    · simp [h_oob] at h_outer
    · simp only [h_oob, Bool.false_eq_true, ↓reduceIte, pure, Pure.pure, Except.pure,
        Except.ok.injEq] at h_outer
      simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      have h_bs_nat : allocation.byteSize.bytes.toNat = allocation.size.bytes.toNat := rfl
      have h_fOuter_le : fOuter.bytes.toNat ≤ allocation.byteSize.bytes.toNat := by omega
      have h_fOuter_raw : fOuter.bytes.toNat ≤ allocation.rawBytes.size := by omega
      have h_fInner_raw : fInner.bytes.toNat ≤ allocation.rawBytes.size := by omega
      unfold Allocation.getBytesUnchecked
      rw [checkedSlice_ok allocation rInner fInner storage h_inner_end h_mid (by omega)]
      subst h_outer
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_left h_fOuter_raw, Nat.min_eq_left h_fInner_raw]
        omega
      · intro i hi1 hi2
        rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_extract]
        have h_idx_eq : rOuter.start.bytes.toNat + ((rInner.start.bytes.toNat - rOuter.start.bytes.toNat) + i) =
            rInner.start.bytes.toNat + i := by omega
        simp only [h_idx_eq]

theorem getBytesUnchecked_split (allocation : Allocation P E)
    (r1 r2 r12 : AllocRange) (mid fin : Size) (b1 b2 : Array UInt8)
    (h_end1 : r1.endExclusive = .ok mid)
    (h_start2 : r2.start = mid)
    (h_end2 : r2.endExclusive = .ok fin)
    (h_start12 : r12.start = r1.start)
    (h_end12 : r12.endExclusive = .ok fin)
    (h_lo1 : r1.start.bytes.toNat ≤ mid.bytes.toNat)
    (h_lo2 : mid.bytes.toNat ≤ fin.bytes.toNat)
    (h_get1 : allocation.getBytesUnchecked r1 = .ok b1)
    (h_get2 : allocation.getBytesUnchecked r2 = .ok b2) :
    allocation.getBytesUnchecked r12 = .ok (b1 ++ b2) := by
  have h_chk2 := h_get2
  unfold Allocation.getBytesUnchecked checkedSlice at h_chk2
  by_cases h_mis : allocation.rawBytes.size != allocation.size.bytes.toNat
  · simp [h_mis, bind, Bind.bind, Except.bind] at h_chk2
  · have h_raw_sz : allocation.rawBytes.size = allocation.size.bytes.toNat := eq_of_not_bne h_mis
    have storage : allocation.len = allocation.byteSize.bytes.toNat := h_raw_sz
    simp only [h_mis, Bool.false_eq_true, ↓reduceIte, h_end2, Except.mapError,
      bind, Bind.bind, Except.bind] at h_chk2
    by_cases h_oob : r2.start.bytes > fin.bytes || fin.bytes > allocation.size.bytes
    · simp [h_oob] at h_chk2
    · simp only [Bool.or_eq_true, not_or, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt] at h_oob
      have h_bs_nat : allocation.byteSize.bytes.toNat = allocation.size.bytes.toNat := rfl
      have h_fin_ib : fin.bytes.toNat ≤ allocation.byteSize.bytes.toNat := by omega
      have h_fin_raw : fin.bytes.toNat ≤ allocation.rawBytes.size := by omega
      have h_mid_raw : mid.bytes.toNat ≤ allocation.rawBytes.size := by omega
      have hs1 := checkedSlice_ok allocation r1 mid storage h_end1 h_lo1 (by omega)
      have hs2 := checkedSlice_ok allocation r2 fin storage h_end2 (by rw [h_start2]; exact h_lo2) h_fin_ib
      have hs12 := checkedSlice_ok allocation r12 fin storage h_end12 (by rw [h_start12]; omega) h_fin_ib
      unfold Allocation.getBytesUnchecked at h_get1 h_get2 ⊢
      rw [hs1] at h_get1
      rw [hs2] at h_get2
      injection h_get1 with hb1
      injection h_get2 with hb2
      subst hb1; subst hb2
      rw [hs12, h_start12, h_start2]
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_extract, Nat.min_eq_left h_fin_raw]
        omega
      · intro i hi1 hi2
        have hi_lt : i < fin.bytes.toNat - r1.start.bytes.toNat := by
          rw [Array.size_extract, Nat.min_eq_left h_fin_raw] at hi1; exact hi1
        by_cases h_left : i < mid.bytes.toNat - r1.start.bytes.toNat
        · have h_sz1 : (allocation.rawBytes.extract r1.start.bytes.toNat mid.bytes.toNat).size =
              mid.bytes.toNat - r1.start.bytes.toNat := by
            simp [Array.size_extract, Nat.min_eq_left h_mid_raw]
          rw [Array.getElem_append_left (by rw [h_sz1]; exact h_left),
            Array.getElem_extract, Array.getElem_extract]
        · have h_sz1 : (allocation.rawBytes.extract r1.start.bytes.toNat mid.bytes.toNat).size =
              mid.bytes.toNat - r1.start.bytes.toNat := by
            simp [Array.size_extract, Nat.min_eq_left h_mid_raw]
          rw [Array.getElem_append_right (by rw [h_sz1]; omega),
            Array.getElem_extract, Array.getElem_extract]
          have h_idx_eq : mid.bytes.toNat +
              (i - (allocation.rawBytes.extract r1.start.bytes.toNat mid.bytes.toNat).size) =
              r1.start.bytes.toNat + i := by omega
          simp only [h_idx_eq]

private theorem targetUIntBytes_eq_ofFn (layout : TargetDataLayout) (size : Size) (bits : U128)
    (limit : size.bytes.toNat ≤ 16) :
    targetUIntBytes layout size bits =
      .ok (Array.ofFn (fun i : Fin size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else size.bytes.toNat - i.1 - 1))) % 256))) := by
  let byteFn : Nat → UInt8 := fun index =>
    UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))) % 256)
  have h_loop : ∀ (indices : List Nat) (acc : Array UInt8),
      (forIn indices acc (fun index cur =>
        (Except.ok (ForInStep.yield (cur.push (byteFn index))) :
          Except AllocError (ForInStep (Array UInt8))))) =
      .ok (acc ++ (indices.map byteFn).toArray) := by
    intro indices
    induction indices with
    | nil =>
      intro acc
      simp [List.forIn_nil, Pure.pure, Except.pure]
    | cons idx rest ih =>
      intro acc
      rw [List.forIn_cons]
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [ih (acc.push (byteFn idx))]
      apply congrArg Except.ok
      apply Array.ext
      · simp [Array.size_append]
      · intro k hk1 hk2
        by_cases hk : k < acc.size
        · rw [Array.getElem_append_left (by simp [Array.size_push]; omega),
            Array.getElem_push_lt hk, Array.getElem_append_left hk]
        · by_cases hk_eq : k = acc.size
          · subst hk_eq
            rw [Array.getElem_append_left (by simp [Array.size_push]),
              Array.getElem_push_eq, Array.getElem_append_right (Nat.le_refl _)]
            simp
          · rw [Array.getElem_append_right (by simp [Array.size_push]; omega),
              Array.getElem_append_right (by omega)]
            simp only [Array.size_push, List.map_cons, List.getElem_toArray, List.getElem_cons]
            have h_pos : k - acc.size = (k - (acc.size + 1)) + 1 := by omega
            simp [h_pos]
  have small : ¬size.bytes > 16 := by
    simp only [UInt64.lt_iff_toNat_lt]
    exact Nat.not_lt.mpr limit
  unfold targetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_inst := h_loop (List.range' 0 [:size.bytes.toNat].size) #[]
  dsimp only [byteFn] at h_inst
  change (forIn (List.range' 0 [:size.bytes.toNat].size) #[] (fun index cur =>
    Except.ok (ForInStep.yield (cur.push (UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))) % 256))))) >>=
    Except.ok) = _
  rw [h_inst]
  simp only [Bind.bind, Except.bind, Array.empty_append]
  apply congrArg Except.ok
  apply Array.ext
  · simp [Std.Legacy.Range.size]
  · intro i hi1 hi2
    simp [List.getElem_range']

private theorem readTargetUInt_eq_foldl (layout : TargetDataLayout) (bytes : Array UInt8)
    (limit : bytes.size ≤ 16) :
    readTargetUInt layout bytes =
      .ok (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc index =>
        acc + (bytes[index]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then index else bytes.size - index - 1))) 0)) := by
  have h_loop : ∀ (indices : List Nat) (acc : Nat),
      (∀ idx ∈ indices, idx < bytes.size) →
      (forIn indices acc (fun index value =>
        (match bytes[index]? with
          | some byte =>
            pure (ForInStep.yield (value + byte.toNat * 2 ^ (8 *
              (if layout.endian == .little then index else bytes.size - index - 1))))
          | _ => do
            throw (.invalidSliceEndpoints index (index + 1) bytes.size)
            pure (ForInStep.yield value) :
          Except AllocError (ForInStep Nat)))) =
      .ok (indices.foldl (fun v index =>
        v + (bytes[index]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then index else bytes.size - index - 1))) acc) := by
    intro indices
    induction indices with
    | nil =>
      intro acc _
      rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < bytes.size := h_in idx (List.mem_cons_self ..)
      have h_get : bytes[idx]? = some (bytes[idx]'h_ib) := Array.getElem?_eq_getElem h_ib
      rw [List.forIn_cons, List.foldl_cons]
      simp only [h_get, Option.getD_some, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  have small : ¬bytes.size > 16 := Nat.not_lt.mpr limit
  unfold readTargetUInt
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_rng_eq : List.range' [0:bytes.size].start [0:bytes.size].size [0:bytes.size].step =
      List.range bytes.size := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  rw [h_rng_eq]
  rw [h_loop (List.range bytes.size) 0 (fun idx h => List.mem_range.mp h)]
  rfl

private theorem digit_step_mod (val m : Nat) :
    val % 2 ^ (8 * m) + ((val / 2 ^ (8 * m)) % 256) * 2 ^ (8 * m) =
      val % 2 ^ (8 * (m + 1)) := by
  let P := 2 ^ (8 * m)
  have hP_pos : 0 < P := Nat.two_pow_pos (8 * m)
  let r := val % P
  let d := (val / P) % 256
  let q := (val / P) / 256
  have hr : r < P := Nat.mod_lt val hP_pos
  have hd : d < 256 := Nat.mod_lt _ (by decide)
  have hd_le : d ≤ 255 := by omega
  have h_dp : d * P ≤ 255 * P := Nat.mul_le_mul_right P hd_le
  have h_sum_lt : r + d * P < P * 256 := by omega
  have h_div1 : P * (val / P) + r = val := Nat.div_add_mod val P
  have h_div2 : 256 * q + d = val / P := Nat.div_add_mod (val / P) 256
  have h_pow_succ : 2 ^ (8 * (m + 1)) = P * 256 := by
    have he : 8 * (m + 1) = 8 * m + 8 := by omega
    rw [he, Nat.pow_add]
  have h_val_decomp : val = (r + d * P) + (P * 256) * q := by
    calc
      val = P * (val / P) + r := h_div1.symm
      _ = P * (256 * q + d) + r := by rw [← h_div2]
      _ = (r + d * P) + (P * 256) * q := by
        simp [Nat.left_distrib, Nat.mul_comm, Nat.mul_left_comm,
          Nat.add_assoc, Nat.add_comm]
  have h_rhs : val % 2 ^ (8 * (m + 1)) = ((r + d * P) + (P * 256) * q) % (P * 256) := by
    rw [h_pow_succ]
    exact congrArg (· % (P * 256)) h_val_decomp
  rw [h_rhs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_sum_lt]

private theorem foldl_add_init (xs : List Nat) (g : Nat → Nat) (init : Nat) :
    xs.foldl (fun acc x => acc + g x) init =
      init + xs.foldl (fun acc x => acc + g x) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + g x), ih (g x), Nat.add_assoc]

private theorem endian_digits_fold_mod (endian : Endian) (val n : Nat) :
    (List.range n).foldl (fun acc idx =>
      acc + ((val / 2 ^ (8 * (if endian == .little then idx else n - idx - 1))) % 256) *
        2 ^ (8 * (if endian == .little then idx else n - idx - 1))) 0 =
      val % 2 ^ (8 * n) := by
  cases endian with
  | little =>
    simp only [beq_self_eq_true, ↓reduceIte]
    induction n with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      exact digit_step_mod val m
  | big =>
    have h_be : (Endian.big == Endian.little) = false := rfl
    simp only [h_be, Bool.false_eq_true, ↓reduceIte]
    induction n with
    | zero => simp [Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hm0 : m + 1 - 0 - 1 = m := by omega
      simp only [Nat.zero_add, hm0]
      have h_fn_eq : (fun acc (x : Nat) =>
          acc + ((val / 2 ^ (8 * (m + 1 - x.succ - 1))) % 256) *
            2 ^ (8 * (m + 1 - x.succ - 1))) =
        (fun acc (x : Nat) =>
          acc + ((val / 2 ^ (8 * (m - x - 1))) % 256) * 2 ^ (8 * (m - x - 1))) := by
        funext acc x
        have hx : m + 1 - x.succ - 1 = m - x - 1 := by omega
        rw [hx]
      rw [h_fn_eq, foldl_add_init, ih, Nat.add_comm]
      exact digit_step_mod val m

private theorem readTargetUInt_ofFn_mod (layout : TargetDataLayout) (n val : Nat)
    (limit : n ≤ 16) :
    readTargetUInt layout (Array.ofFn (fun i : Fin n =>
      UInt8.ofNat ((val / 2 ^ (8 *
        (if layout.endian == .little then i.1 else n - i.1 - 1))) % 256))) =
      .ok (BitVec.ofNat 128 (val % 2 ^ (8 * n))) := by
  let arr := Array.ofFn (fun i : Fin n =>
    UInt8.ofNat ((val / 2 ^ (8 *
      (if layout.endian == .little then i.1 else n - i.1 - 1))) % 256))
  have h_sz : arr.size = n := Array.size_ofFn ..
  rw [readTargetUInt_eq_foldl layout arr (by rw [h_sz]; exact limit)]
  rw [h_sz]
  apply congrArg Except.ok
  apply congrArg (BitVec.ofNat 128)
  have h_congr : ∀ (xs : List Nat) (acc : Nat),
      (∀ idx ∈ xs, idx < n) →
      xs.foldl (fun a idx =>
        a + (arr[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else n - idx - 1))) acc =
      xs.foldl (fun a idx =>
        a + ((val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256) *
          2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < n := h_in idx (List.mem_cons_self ..)
      have h_ib_arr : idx < arr.size := by rw [h_sz]; exact h_ib
      have h_elem : (arr[idx]?.getD 0).toNat =
          (val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256 := by
        rw [Array.getElem?_eq_getElem h_ib_arr, Option.getD_some]
        dsimp only [arr]
        rw [Array.getElem_ofFn]
        have h_lt256 : (val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256 < 256 :=
          Nat.mod_lt _ (by decide)
        simp [UInt8.toNat_ofNat']
      simp only [List.foldl_cons, h_elem]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  rw [h_congr (List.range n) 0 (fun idx h => List.mem_range.mp h)]
  exact endian_digits_fold_mod layout.endian val n

theorem getBytesStripProvenance_uninit_err [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.getBytesStripProvenance layout range =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  unfold Allocation.getBytesStripProvenance
  simp only [Allocation.initializationMask] at h_uninit
  simp [h_uninit, bind, Bind.bind, Except.bind, Except.mapError, throw, MonadExceptOf.throw, throwThe]

theorem getBytesStripProvenance_ok [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.getBytesStripProvenance layout range = allocation.getBytesUnchecked range := by
  unfold Allocation.getBytesStripProvenance Allocation.getBytesUnchecked pointerSize
  simp only [Allocation.initializationMask] at h_init
  simp only [Allocation.provenanceMap] at h_prov
  rcases h_prov with h_addr | h_empty
  · simp [h_init, h_addr, bind, Bind.bind, Except.bind, Except.mapError]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp [h_init, h_addr, bind, Bind.bind, Except.bind, Except.mapError]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_init, h_addr_f, h_empty, bind, Bind.bind, Except.bind, Except.mapError]

theorem readScalar_uninit_err [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange) (readProvenance : Bool)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.readScalar layout range readProvenance =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  unfold Allocation.readScalar
  simp only [Allocation.initializationMask] at h_uninit
  simp [h_uninit, bind, Bind.bind, Except.bind, Except.mapError, throw, MonadExceptOf.throw, throwThe]

theorem readScalar_int_of_bytes [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bytes : Array UInt8)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (h_limit : bytes.size ≤ 16)
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc idx =>
        acc + (bytes[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else bytes.size - idx - 1))) 0))
        range.size).mapError AllocError.scalar := by
  unfold Allocation.readScalar pointerSize
  unfold Allocation.getBytesUnchecked at h_slice
  simp only [Allocation.initializationMask] at h_init
  simp only [Allocation.provenanceMap] at h_prov
  have h_read := readTargetUInt_eq_foldl layout bytes h_limit
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  rcases h_prov with h_addr | h_empty
  · simp [h_addr]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp [h_addr]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_addr_f, h_empty]

theorem readScalar_int_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  unfold Allocation.readScalar pointerSize
  unfold Allocation.getBytesUnchecked at h_slice
  simp only [Allocation.initializationMask] at h_init
  simp only [Allocation.provenanceMap] at h_prov
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  rcases h_prov with h_addr | h_empty
  · simp [h_addr]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · simp [h_addr]
    · have h_addr_f : PointerProvenance.offsetIsAddr (Prov := P) = false :=
        Bool.eq_false_iff.mpr h_addr
      simp [h_addr_f, h_empty]

theorem readScalar_ptr_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (ptr : Pointer P)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_off_bound : ptr.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range true = .ok (Scalar.fromPointer layout ptr) := by
  unfold Allocation.readScalar pointerSize
  unfold Allocation.getBytesUnchecked at h_slice
  simp only [Allocation.initializationMask] at h_init
  simp only [Allocation.provenanceMap] at h_prov
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat ptr.offset.bytes.toNat h_limit
  rw [Nat.mod_eq_of_lt h_off_bound] at h_read
  have h_u64_lt := ptr.offset.bytes.toNat_lt
  have h_lt128 : ptr.offset.bytes.toNat < 2 ^ 128 := by omega
  have h_bv_nat : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt128]
  have h_not_gt : ¬(18446744073709551615 < ptr.offset.bytes.toNat) := by omega
  have h_ptr_eta : Pointer.new ptr.provenance (Size.ofBytes ptr.offset.bytes) = ptr := by
    cases ptr with
    | mk off prov =>
      cases off with
      | mk b =>
        rfl
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  simp [h_ptr_sz, h_prov, h_bv_nat, h_not_gt, h_ptr_eta,
    ]

theorem readScalar_ptr_none_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok none)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range true =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  unfold Allocation.readScalar pointerSize
  unfold Allocation.getBytesUnchecked at h_slice
  simp only [Allocation.initializationMask] at h_init
  simp only [Allocation.provenanceMap] at h_prov
  have h_read := readTargetUInt_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  simp only [h_init, h_slice, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_read]
  simp [h_ptr_sz, h_prov]

theorem writeScalar_spec (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr range.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range true = .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      (∀ b, converted = .bits b →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat ((b.toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      (∀ p, converted = .pointer p →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat (((BitVec.ofNat 128 p.offset.bytes.toNat).toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (range.start.bytes.toNat + range.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ range.start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
    have := allocation.byteSize.bytes.toNat_lt; omega
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint (by omega) (by rw [maskLength]; simpa only [finishNat] using bound)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      (by omega) (by rw [maskLength]; simpa only [finishNat] using bound) maskOk
  let bits : U128 := match converted with
    | .bits b => b
    | .pointer p => BitVec.ofNat 128 p.offset.bytes.toNat
  let data := Array.ofFn (fun i : Fin range.size.bytes.toNat =>
    UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256))
  have dataOk : targetUIntBytes layout range.size bits = .ok data :=
    targetUIntBytes_eq_ofFn layout range.size bits width
  have dataSize : data.size = range.size.bytes.toNat := Array.size_ofFn ..
  let wStart := range.start.bytes.toNat
  let wFin := range.start.bytes.toNat + range.size.bytes.toNat
  let spliced := allocation.rawBytes.extract 0 wStart ++ data ++
    allocation.rawBytes.extract wFin allocation.rawBytes.size
  have h_wFin_raw : wFin ≤ allocation.rawBytes.size := by
    change wFin ≤ allocation.len; omega
  have bytesLength : spliced.size = allocation.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ allocation.rawBytes.size),
      Nat.min_self, Nat.sub_zero, dataSize]
    change _ = allocation.byteSize.bytes.toNat
    change allocation.rawBytes.size = allocation.byteSize.bytes.toNat at storage
    omega
  have h_clear_raw : allocation.provenance.clear range allocation.rawBytes (pointerSize layout) =
      .ok () cleared :=
    clear allocation.rawBytes (getBytesUnchecked_full_rawBytes allocation storage)
  let updated : Allocation P E :=
    ⟨spliced, allocation.byteSize, nextProvenance, mask, allocation.align,
      allocation.mutability, allocation.extra, allocation.nativeBuffer⟩
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  have h_get_data : updated.getBytesUnchecked range = .ok data := by
    unfold Allocation.getBytesUnchecked
    have h_fin_ib : finish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat
      simpa only [finishNat] using bound
    rw [checkedSlice_ok updated range finish h_upd_storage endpoint (by omega) h_fin_ib]
    rw [finishNat]
    exact congrArg Except.ok
      (splice_extract_exact allocation.rawBytes data wStart wFin
        (by dsimp only [wStart, wFin]; omega) h_wFin_raw
        (by rw [dataSize]; dsimp only [wStart, wFin]; omega))
  refine ⟨updated, ?_, rfl, bytesLength.trans storage.symm, rfl, rfl, rfl, rfl,
    maskSize, maskWF, maskOk, h_is_init, rfl,
    fun b hb => by subst hb; exact h_get_data,
    fun p hp => by subst hp; exact h_get_data,
    ?_⟩
  · have slice := checkedSlice_ok allocation range finish storage endpoint (by omega)
      (by simpa only [finishNat] using bound)
    simp only [Allocation.initializationMask] at maskOk
    unfold Allocation.writeScalar
    simp only [mutable, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, conversion,
      Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [slice, maskOk]
    rw [h_clear_raw]
    dsimp only [spliced, wStart, wFin, Allocation.byteSize] at bytesLength
    cases converted with
    | bits payload =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      simp [insert, updated, spliced, wStart, wFin, mutable]
      rfl
    | pointer pointer =>
      dsimp only [bits] at dataOk
      rw [dataOk]
      simp only [bytesLength, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rcases insert with ⟨sizeEq, inserted⟩
      have sizeEq' : range.size = pointerSize layout := sizeEq
      have inserted' : cleared.insertPtr range.start pointer.provenance (pointerSize layout) =
          .ok () nextProvenance := inserted
      have h_sz_bne : (range.size != pointerSize layout) = false := by
        rw [sizeEq']
        exact bne_self_eq_false (pointerSize layout)
      simp only [h_sz_bne, Bool.false_eq_true, ↓reduceIte]
      rw [inserted']
      dsimp only [updated, spliced, wStart, wFin]
      rw [mutable]
      rfl
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    unfold Allocation.getBytesUnchecked
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok allocation qRange qFin storage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ allocation.rawBytes.size := by
      change qFin.bytes.toNat ≤ allocation.len; omega
    exact congrArg Except.ok
      (splice_extract_disjoint allocation.rawBytes data wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (by omega) h_wFin_raw h_qlo h_qfin_raw (by rw [dataSize]; omega) h_disj)

theorem writeBytes_zero_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E)
    (h_empty : bytes.size = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (inBounds : start.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Allocation.writeBytes start bytes ptrSize allocation = .ok () allocation := by
  have h_sfa : sizeForArray 0 = .ok Size.ZERO := rfl
  have h_end : (allocRange start Size.ZERO).endExclusive = .ok start := by
    cases start
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  have h_slice := checkedSlice_ok allocation (allocRange start Size.ZERO) start storage h_end
    (Nat.le_refl _) inBounds
  unfold Allocation.writeBytes
  rw [h_empty, h_sfa]
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, h_slice]
  rfl

theorem writeBytes_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (h_nonempty : 0 < bytes.size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : start.bytes.toNat + bytes.size ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) fullBytes ptrSize =
        .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeBytes start bytes ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) true =
        .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) =
        .ok bytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (start.bytes.toNat + bytes.size ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have h_u64_alloc := allocation.byteSize.bytes.toNat_lt
  have h_bsz_lt : bytes.size < 2 ^ 64 := by omega
  have h_not_gt_max : ¬(bytes.size > maxU64Nat) := by unfold maxU64Nat; omega
  let writeSize := Size.ofBytes (UInt64.ofNat bytes.size)
  have h_wsz_nat : writeSize.bytes.toNat = bytes.size := by
    simp [writeSize, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_bsz_lt]
  have h_sfa : sizeForArray bytes.size = .ok writeSize := by
    unfold sizeForArray
    simp [h_not_gt_max, h_wsz_nat, writeSize, pure, Pure.pure, Except.pure]
  have h_wsz_nz : (writeSize.bytes == 0) = false := by
    apply beq_false_of_ne
    intro h0
    have : writeSize.bytes.toNat = 0 := by simp [h0]
    omega
  let range := allocRange start writeSize
  have fits : start.bytes.toNat + writeSize.bytes.toNat < 2 ^ 64 := by omega
  let finish := Size.ofBytes (start.bytes + writeSize.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end range allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size start writeSize fits)
  have finishNat : finish.bytes.toNat = start.bytes.toNat + bytes.size := by
    have h_def : finish.bytes.toNat = (start.bytes + writeSize.bytes).toNat := rfl
    rw [h_def, UInt64.toNat_add, Nat.mod_eq_of_lt fits, h_wsz_nat]
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint (by dsimp only [range, allocRange]; omega)
      (by rw [maskLength]; omega)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      (by dsimp only [range, allocRange]; omega) (by rw [maskLength]; omega) maskOk
  have h_slice := checkedSlice_ok allocation range finish storage endpoint
    (by dsimp only [range, allocRange]; omega) (by omega)
  have h_clear_raw : allocation.provenance.clear range allocation.rawBytes ptrSize =
      .ok () nextProvenance :=
    clear allocation.rawBytes (getBytesUnchecked_full_rawBytes allocation storage)
  let wStart := start.bytes.toNat
  let wFin := finish.bytes.toNat
  let spliced := allocation.rawBytes.extract 0 wStart ++ bytes ++
    allocation.rawBytes.extract wFin allocation.rawBytes.size
  have h_wFin_raw : wFin ≤ allocation.rawBytes.size := by
    change wFin ≤ allocation.len; omega
  have bytesLength : spliced.size = allocation.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ allocation.rawBytes.size),
      Nat.min_self, Nat.sub_zero]
    change _ = allocation.byteSize.bytes.toNat
    change allocation.rawBytes.size = allocation.byteSize.bytes.toNat at storage
    omega
  let updated : Allocation P E :=
    ⟨spliced, allocation.byteSize, nextProvenance, mask, allocation.align,
      allocation.mutability, allocation.extra, allocation.nativeBuffer⟩
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  refine ⟨updated, ?_, rfl, bytesLength.trans storage.symm, rfl, rfl, rfl, rfl,
    maskSize, maskWF, maskOk, h_is_init, rfl, ?_, ?_⟩
  · simp only [Allocation.initializationMask] at maskOk
    dsimp only [range] at maskOk h_clear_raw endpoint h_slice
    unfold Allocation.writeBytes setInitialization overwriteRawBytes
    rw [h_sfa]
    dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
    change (match checkedSlice allocation (allocRange start writeSize) with
      | .error reason => EStateM.Result.error reason allocation
      | .ok _ => _) = _
    rw [h_slice]
    simp only [h_wsz_nz, Bool.false_eq_true, ↓reduceIte, mutable, bne_self_eq_false,
      maskOk, Except.mapError, Except.bind, Except.pure]
    rw [h_clear_raw]
    dsimp only
    rw [endpoint]
    dsimp only [Except.mapError, Except.bind, allocRange]
    have h_len_chk : (spliced.size != allocation.size.bytes.toNat) = false := by
      change (spliced.size != allocation.byteSize.bytes.toNat) = false
      rw [bytesLength]
      exact bne_self_eq_false _
    dsimp only [spliced, wStart, wFin, allocRange] at h_len_chk
    simp only [h_len_chk, Bool.false_eq_true, ↓reduceIte]
    dsimp only [updated, spliced, wStart, wFin]
    rw [mutable]
    rfl
  · unfold Allocation.getBytesUnchecked
    have h_fin_ib : finish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat; omega
    rw [checkedSlice_ok updated range finish h_upd_storage endpoint
      (by dsimp only [range, allocRange]; omega) h_fin_ib]
    exact congrArg Except.ok
      (splice_extract_exact allocation.rawBytes bytes wStart wFin
        (by omega) h_wFin_raw (by omega))
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    unfold Allocation.getBytesUnchecked
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok allocation qRange qFin storage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ allocation.rawBytes.size := by
      change qFin.bytes.toNat ≤ allocation.len; omega
    exact congrArg Except.ok
      (splice_extract_disjoint allocation.rawBytes bytes wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (by omega) h_wFin_raw h_qlo h_qfin_raw (by omega)
        (by dsimp only [wStart, wFin]; omega))

theorem writeUninit_zero_spec (range : AllocRange) (finish ptrSize : Size)
    (allocation : Allocation P E)
    (h_zero : range.size.bytes = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Allocation.writeUninit range ptrSize allocation = .ok () allocation := by
  have h_slice := checkedSlice_ok allocation range finish storage endEq startLe inBounds
  unfold Allocation.writeUninit
  simp [h_slice, h_zero, Id.run, pure, Pure.pure]

theorem writeUninit_spec (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (nonzero : range.size.bytes ≠ 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes ptrSize = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeUninit range ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range false = .ok updated.initializationMask ∧
      updated.provenanceMap = nextProvenance ∧
      ∀ (anyRange : AllocRange),
        updated.getBytesUnchecked anyRange = allocation.getBytesUnchecked anyRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
    have := allocation.byteSize.bytes.toNat_lt; omega
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro zero; exact nonzero (UInt64.toNat_inj.mp zero))
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish false
      maskValid endpoint (by omega) (by rw [maskLength]; simpa only [finishNat] using inBounds)
  have h_slice := checkedSlice_ok allocation range finish storage endpoint (by omega)
    (by simpa only [finishNat] using inBounds)
  have h_clear_raw : allocation.provenance.clear range allocation.rawBytes ptrSize =
      .ok () nextProvenance :=
    clear allocation.rawBytes (getBytesUnchecked_full_rawBytes allocation storage)
  let updated : Allocation P E :=
    ⟨allocation.rawBytes, allocation.byteSize, nextProvenance, mask, allocation.align,
      allocation.mutability, allocation.extra, allocation.nativeBuffer⟩
  refine ⟨updated, ?_, rfl, rfl, rfl, rfl, rfl, rfl, maskSize, maskWF, maskOk, rfl, fun _ => rfl⟩
  simp only [Allocation.initializationMask] at maskOk
  have h_nz_beq : (range.size.bytes == 0) = false := beq_false_of_ne nonzero
  unfold Allocation.writeUninit setInitialization
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure, h_slice, h_nz_beq,
    Bool.false_eq_true, ↓reduceIte, mutable, bne_self_eq_false,
    maskOk, Except.mapError, Except.bind, Except.pure]
  rw [h_clear_raw]
  simp [updated, mutable]
  rfl

theorem copyRepeatedly_initialized_spec
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart totalSize ptrSize : Size)
    (repeatCount : UInt64) (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_repPos : 0 < repeatCount.toNat)
    (h_mul : Size.mul sourceRange.size repeatCount = .ok totalSize)
    (h_repMode : repeatCount > 1 → nonoverlapping = true)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + totalSize.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart totalSize) stFull ptrSize =
        .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) repeatCount = .ok () finalProv) :
    ∃ updated,
      Allocation.copyRepeatedly source sourceRange destStart repeatCount
        ptrSize sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart totalSize) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart totalSize) =
        .ok ((List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange := by
  have h_src_pos : 0 < sourceRange.size.bytes.toNat := Nat.pos_of_ne_zero (by
    intro h0; exact srcNonzero (UInt64.toNat_inj.mp h0))
  have h_src_fits : sourceRange.start.bytes.toNat + sourceRange.size.bytes.toNat < 2 ^ 64 := by
    unfold AllocRange.endExclusive AllocRange.end Size.add at srcEnd
    by_cases hw : sourceRange.start.bytes + sourceRange.size.bytes < sourceRange.start.bytes
    · simp [hw, Except.mapError] at srcEnd
    · have hnw : ¬((sourceRange.start.bytes + sourceRange.size.bytes).toNat <
          sourceRange.start.bytes.toNat) := by simpa [UInt64.lt_iff_toNat_lt] using hw
      have := sourceRange.start.bytes.toNat_lt
      have := sourceRange.size.bytes.toNat_lt
      by_cases hlt : sourceRange.start.bytes.toNat + sourceRange.size.bytes.toNat < 2 ^ 64
      · exact hlt
      · rw [UInt64.toNat_add] at hnw; omega
  have h_srcFin_nat : srcFinish.bytes.toNat =
      sourceRange.start.bytes.toNat + sourceRange.size.bytes.toNat := by
    unfold AllocRange.endExclusive AllocRange.end Size.add at srcEnd
    by_cases hw : sourceRange.start.bytes + sourceRange.size.bytes < sourceRange.start.bytes
    · simp [hw, Except.mapError] at srcEnd
    · simp only [hw, ↓reduceIte, Except.mapError, Except.ok.injEq] at srcEnd
      subst srcEnd
      simp only [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_src_fits]
  have h_srcBytes_sz : srcBytes.size = sourceRange.size.bytes.toNat := by
    have hs := checkedSlice_ok source sourceRange srcFinish srcStorage srcEnd (by omega) srcInBounds
    unfold Allocation.getBytesUnchecked at srcSlice
    rw [hs] at srcSlice
    injection srcSlice with h_eq
    subst h_eq
    have h_f_raw : srcFinish.bytes.toNat ≤ source.rawBytes.size := by
      change srcFinish.bytes.toNat ≤ source.len; omega
    rw [Array.size_extract, Nat.min_eq_left h_f_raw, h_srcFin_nat]
    omega
  have h_mul_nat : totalSize.bytes.toNat =
      sourceRange.size.bytes.toNat * repeatCount.toNat := by
    unfold Size.mul at h_mul
    have h_rc_nz : (repeatCount != 0) = true := by
      apply bne_iff_ne.mpr
      intro h0; simp [h0] at h_repPos
    by_cases h_ovf : (sourceRange.size.bytes * repeatCount) / repeatCount != sourceRange.size.bytes
    · simp [h_rc_nz, h_ovf] at h_mul
    · simp only [h_rc_nz, Bool.true_and, h_ovf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h_mul
      subst h_mul
      have h_div_eq : (sourceRange.size.bytes * repeatCount) / repeatCount = sourceRange.size.bytes :=
        eq_of_not_bne h_ovf
      have h_prod_lt : sourceRange.size.bytes.toNat * repeatCount.toNat < 2 ^ 64 := by
        have h_le_u64 := (sourceRange.size.bytes * repeatCount).toNat_lt
        have h_div_nat : ((sourceRange.size.bytes * repeatCount) / repeatCount).toNat =
            (sourceRange.size.bytes * repeatCount).toNat / repeatCount.toNat := UInt64.toNat_div ..
        rw [h_div_eq] at h_div_nat
        have := Nat.mul_le_of_le_div repeatCount.toNat _ _ (Nat.le_of_eq h_div_nat)
        have h_rem := Nat.div_add_mod (sourceRange.size.bytes * repeatCount).toNat repeatCount.toNat
        omega
      simp only [Size.ofBytes, UInt64.toNat_mul, Nat.mod_eq_of_lt h_prod_lt]
  have h_tot_pos : 0 < totalSize.bytes.toNat := by
    rw [h_mul_nat]; exact Nat.mul_pos h_src_pos h_repPos
  have h_tot_nz : (totalSize.bytes == 0) = false := by
    apply beq_false_of_ne
    intro h0; have : totalSize.bytes.toNat = 0 := by simp [h0]
    omega
  let destRange := allocRange destStart totalSize
  have h_dest_fits : destStart.bytes.toNat + totalSize.bytes.toNat < 2 ^ 64 := by
    have := state.byteSize.bytes.toNat_lt; omega
  let destFinish := Size.ofBytes (destStart.bytes + totalSize.bytes)
  have destEnd : destRange.endExclusive = .ok destFinish := by
    unfold AllocRange.endExclusive AllocRange.end destRange allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (write_add_size destStart totalSize h_dest_fits)
  have h_destFin_nat : destFinish.bytes.toNat = destStart.bytes.toNat + totalSize.bytes.toNat := by
    simp only [destFinish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_dest_fits]
  have h_src_unif : ∀ idx : Size, sourceRange.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < srcFinish.bytes.toNat → source.initializationMask.get idx = .ok true :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff source.initializationMask
      sourceRange srcFinish srcMaskWF srcEnd (by omega)
      (by rw [srcMaskLen]; exact srcInBounds)).1.mp srcInit
  have h_prep_init : source.initializationMask.prepareCopy sourceRange =
      .ok ⟨true, #[sourceRange.size.bytes]⟩ :=
    InitMask.WriteProof.prepareCopy_of_uniform source.initializationMask
      sourceRange srcFinish true srcMaskWF srcEnd (by omega)
      (by rw [srcMaskLen]; exact srcInBounds) h_src_unif
  have h_prep_prov : source.provenance.prepareCopy sourceRange source.rawBytes ptrSize = .ok provCopy :=
    h_prepProv source.rawBytes (getBytesUnchecked_full_rawBytes source srcStorage)
  obtain ⟨mask1, mask1Ok, mask1Len, mask1WF⟩ :=
    InitMask.WriteProof.set_range_exists state.initializationMask destRange destFinish true
      destMaskWF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [destMaskLen]; omega)
  obtain ⟨mask2, mask2Ok, mask2Len, mask2WF⟩ :=
    InitMask.WriteProof.set_range_exists mask1 destRange destFinish true
      mask1WF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [mask1Len, destMaskLen]; omega)
  have h_apply_init : mask1.applyCopy ⟨true, #[sourceRange.size.bytes]⟩
      (allocRange destStart sourceRange.size) repeatCount = .ok mask2 := by
    rw [InitMask.WriteProof.applyCopy_singleton mask1 destStart sourceRange.size totalSize
      repeatCount true srcNonzero h_mul]
    exact mask2Ok
  have h_mask2_isInit : mask2.isRangeInitialized destRange = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true mask1 mask2 destRange destFinish
      mask1WF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [mask1Len, destMaskLen]; omega) mask2Ok
  have h_clear_raw : state.provenance.clear destRange state.rawBytes ptrSize = .ok () clearedProv :=
    h_clearProv state.rawBytes (getBytesUnchecked_full_rawBytes state destStorage)
  have h_srcSlice_chk : checkedSlice source sourceRange = .ok srcBytes := srcSlice
  have h_destSlice_chk := checkedSlice_ok state destRange destFinish destStorage destEnd
    (by dsimp only [destRange, allocRange]; omega) (by omega)
  let copiedBytes := (List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray
  have h_rep_loop : ∀ (k s : Nat) (acc : Array UInt8),
      forIn (m := Id) (List.range' s k) acc (fun _ cur =>
        pure (ForInStep.yield (cur ++ srcBytes))) =
      acc ++ (List.replicate k srcBytes.toList).flatten.toArray := by
    intro k
    induction k with
    | zero =>
      intro s acc
      simp [List.range', List.forIn_nil, pure, Pure.pure]
    | succ m ih =>
      intro s acc
      rw [List.range'_succ, List.forIn_cons]
      change forIn (m := Id) (List.range' (s + 1) m) (acc ++ srcBytes)
        (fun _ cur => pure (ForInStep.yield (cur ++ srcBytes))) = _
      rw [ih (s + 1) (acc ++ srcBytes)]
      apply Array.ext
      · simp [Array.size_append, List.replicate_succ]
      · intro i hi1 hi2
        have h_toList : (acc ++ srcBytes ++ (List.replicate m srcBytes.toList).flatten.toArray).toList =
            (acc ++ (List.replicate (m + 1) srcBytes.toList).flatten.toArray).toList := by
          simp [Array.toList_append, List.replicate_succ]
        exact List.getElem_of_eq h_toList _
  have h_copied_sz : copiedBytes.size = totalSize.bytes.toNat := by
    have h_len : (List.replicate repeatCount.toNat srcBytes.toList).flatten.length =
        repeatCount.toNat * srcBytes.size := by
      induction repeatCount.toNat with
      | zero => simp
      | succ m ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]
    simp [copiedBytes, h_len, h_srcBytes_sz, h_mul_nat, Nat.mul_comm]
  let wStart := destStart.bytes.toNat
  let wFin := destFinish.bytes.toNat
  let spliced := state.rawBytes.extract 0 wStart ++ copiedBytes ++
    state.rawBytes.extract wFin state.rawBytes.size
  have h_wFin_raw : wFin ≤ state.rawBytes.size := by
    change wFin ≤ state.len; omega
  have bytesLength : spliced.size = state.byteSize.bytes.toNat := by
    simp only [spliced, Array.size_append, Array.size_extract,
      Nat.min_eq_left (by omega : wStart ≤ state.rawBytes.size),
      Nat.min_self, Nat.sub_zero, h_copied_sz]
    change _ = state.byteSize.bytes.toNat
    change state.rawBytes.size = state.byteSize.bytes.toNat at destStorage
    omega
  let updated : Allocation P E :=
    ⟨spliced, state.byteSize, finalProv, mask2, state.align,
      state.mutability, state.extra, state.nativeBuffer⟩
  have h_upd_storage : updated.len = updated.byteSize.bytes.toNat := bytesLength
  have h_mask_get_frame : ∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
      mask2.get idx =
        if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
            idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
          .ok true
        else
          state.initializationMask.get idx := by
    intro idx h_idx_lt
    have h_g2 := InitMask.WriteProof.set_range_get mask1 mask2 destRange destFinish idx true
      mask1WF destEnd (by dsimp only [destRange, allocRange]; omega)
      (by rw [mask1Len, destMaskLen]; omega)
      (by rw [mask1Len, destMaskLen]; exact h_idx_lt) mask2Ok
    have h_g1 := InitMask.WriteProof.set_range_get state.initializationMask mask1
      destRange destFinish idx true destMaskWF destEnd
      (by dsimp only [destRange, allocRange]; omega)
      (by rw [destMaskLen]; omega)
      (by rw [destMaskLen]; exact h_idx_lt) mask1Ok
    have h_dr_start : destRange.start = destStart := rfl
    rw [h_dr_start, h_destFin_nat] at h_g2 h_g1
    by_cases h_in : destStart.bytes.toNat ≤ idx.bytes.toNat ∧
        idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat
    · rw [if_pos_eq h_in] at h_g2 ⊢; exact h_g2
    · rw [if_neg_eq h_in] at h_g2 h_g1 ⊢; exact h_g2.trans h_g1
  have h_mask_range_frame : ∀ (qRange : AllocRange) (qFin : Size),
      qRange.endExclusive = .ok qFin →
      qRange.start.bytes.toNat < qFin.bytes.toNat →
      qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
      (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
        qFin.bytes.toNat ≤ destStart.bytes.toNat) →
      (mask2.isRangeInitialized qRange = .ok (.ok ()) ↔
        state.initializationMask.isRangeInitialized qRange = .ok (.ok ())) := by
    intro qRange qFin h_qend h_qne h_qib h_disj
    have h_disj' : destFinish.bytes.toNat ≤ qRange.start.bytes.toNat ∨
        qFin.bytes.toNat ≤ destRange.start.bytes.toNat := by
      dsimp only [destRange, allocRange]; omega
    exact (InitMask.WriteProof.isRangeInitialized_frame mask1 mask2 destRange qRange
      destFinish qFin true mask1WF destEnd h_qend
      (by dsimp only [destRange, allocRange]; omega) h_qne
      (by rw [mask1Len, destMaskLen]; omega)
      (by rw [mask1Len, destMaskLen]; exact h_qib) h_disj' mask2Ok).trans
      (InitMask.WriteProof.isRangeInitialized_frame state.initializationMask mask1 destRange qRange
        destFinish qFin true destMaskWF destEnd h_qend
        (by dsimp only [destRange, allocRange]; omega) h_qne
        (by rw [destMaskLen]; omega)
        (by rw [destMaskLen]; exact h_qib) h_disj' mask1Ok)
  refine ⟨updated, ?_, rfl, bytesLength.trans destStorage.symm, rfl, rfl, rfl, rfl,
    mask2Len.trans mask1Len, mask2WF, h_mask2_isInit, h_mask_get_frame, h_mask_range_frame,
    rfl, ?_, ?_⟩
  · simp only [Allocation.initializationMask] at h_prep_init mask1Ok
    unfold Allocation.copyRepeatedly prepareForOverwrite setInitialization
      runProvenanceMutation overwriteRawBytes
    simp only [Id.run, bind, Bind.bind, pure, Pure.pure,
      h_srcSlice_chk, h_mul, h_prep_prov, h_prep_init]
    dsimp only [destRange, allocRange] at h_destSlice_chk mask1Ok h_clear_raw destEnd ⊢
    simp only [h_destSlice_chk, h_tot_nz, Bool.false_eq_true, ↓reduceIte,
      destMut, bne_self_eq_false, mask1Ok, Except.mapError, Except.bind, Except.pure,
      h_clear_raw, InitCopy.noBytesInit, Bool.not_true, Bool.false_and]
    have h_first_fits : destStart.bytes.toNat + sourceRange.size.bytes.toNat < 2 ^ 64 := by
      have : sourceRange.size.bytes.toNat * 1 ≤ sourceRange.size.bytes.toNat * repeatCount.toNat :=
        Nat.mul_le_mul_left _ h_repPos
      omega
    let firstFin := Size.ofBytes (destStart.bytes + sourceRange.size.bytes)
    have h_first_end : (allocRange destStart sourceRange.size).endExclusive = .ok firstFin := by
      unfold AllocRange.endExclusive AllocRange.end allocRange
      exact congrArg (Except.mapError MemoryError.sizeError)
        (write_add_size destStart sourceRange.size h_first_fits)
    have h_first_nat : firstFin.bytes.toNat = destStart.bytes.toNat + sourceRange.size.bytes.toNat := by
      simp only [firstFin, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_first_fits]
    have h_rep_chk : (repeatCount > 1 && !nonoverlapping) = false := by
      by_cases h_gt1 : repeatCount > 1
      · simp [h_gt1, h_repMode h_gt1]
      · simp [h_gt1]
    have h_rc_nz_beq : (repeatCount == 0) = false := by
      apply beq_false_of_ne; intro h0; simp [h0] at h_repPos
    have h_len_ne : (spliced.size != state.size.bytes.toNat) = false := by
      change (spliced.size != state.byteSize.bytes.toNat) = false
      rw [bytesLength]; exact bne_self_eq_false _
    dsimp only [spliced, wStart, wFin, copiedBytes] at h_len_ne
    dsimp only [allocRange] at h_first_end h_apply_init h_applyProv
    by_cases h_sn : (sameAllocation && nonoverlapping) = true
    · simp only [Bool.and_eq_true] at h_sn
      have h_d := h_disjSame h_sn.1 h_sn.2
      have h_no_ovl : ¬(sourceRange.start.bytes < firstFin.bytes ∧ destStart.bytes < srcFinish.bytes) := by
        simp only [UInt64.lt_iff_toNat_lt]; omega
      simp only [h_sn, Bool.and_self, ↓reduceIte, srcEnd, h_first_end, h_no_ovl,
        decide_eq_true_eq, Bool.and_eq_true, Bool.false_eq_true,
        h_rc_nz_beq, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have h_loop_inst := h_rep_loop repeatCount.toNat 0 #[]
      dsimp only [pure, Pure.pure] at h_loop_inst
      rw [h_loop_inst]
      simp only [Array.empty_append, destEnd,         h_len_ne, Bool.false_eq_true, ↓reduceIte, h_apply_init, h_applyProv]
      dsimp only [updated, spliced, wStart, wFin, copiedBytes]
      rw [destMut]
      rfl
    · simp only [h_sn, Bool.false_eq_true, ↓reduceIte, h_rep_chk,
        h_rc_nz_beq, Bool.not_false, Bool.false_and, Bool.and_false,
        Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have h_loop_inst := h_rep_loop repeatCount.toNat 0 #[]
      dsimp only [pure, Pure.pure] at h_loop_inst
      rw [h_loop_inst]
      simp only [Array.empty_append, destEnd,         h_len_ne, Bool.false_eq_true, ↓reduceIte, h_apply_init, h_applyProv]
      dsimp only [updated, spliced, wStart, wFin, copiedBytes]
      rw [destMut]
      rfl
  · unfold Allocation.getBytesUnchecked
    have h_destFin_ib : destFinish.bytes.toNat ≤ updated.byteSize.bytes.toNat := by
      change destFinish.bytes.toNat ≤ state.byteSize.bytes.toNat; omega
    rw [checkedSlice_ok updated destRange destFinish h_upd_storage destEnd
      (by dsimp only [destRange, allocRange]; omega) h_destFin_ib]
    exact congrArg Except.ok
      (splice_extract_exact state.rawBytes copiedBytes wStart wFin
        (by omega) h_wFin_raw (by omega))
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    unfold Allocation.getBytesUnchecked
    have h_qib_upd : qFin.bytes.toNat ≤ updated.byteSize.bytes.toNat := h_qib
    rw [checkedSlice_ok updated qRange qFin h_upd_storage h_qend h_qlo h_qib_upd,
      checkedSlice_ok state qRange qFin destStorage h_qend h_qlo h_qib]
    have h_qfin_raw : qFin.bytes.toNat ≤ state.rawBytes.size := by
      change qFin.bytes.toNat ≤ state.len; omega
    exact congrArg Except.ok
      (splice_extract_disjoint state.rawBytes copiedBytes wStart wFin
        qRange.start.bytes.toNat qFin.bytes.toNat
        (by omega) h_wFin_raw h_qlo h_qfin_raw (by omega)
        (by dsimp only [wStart, wFin]; omega))

theorem copy_initialized_spec
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart ptrSize : Size)
    (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart sourceRange.size) stFull ptrSize =
        .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) 1 = .ok () finalProv) :
    ∃ updated,
      Allocation.copy source sourceRange destStart ptrSize
        sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart sourceRange.size) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + sourceRange.size.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart sourceRange.size) = .ok srcBytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange := by
  have h_mul1 : Size.mul sourceRange.size 1 = .ok sourceRange.size := by
    cases sourceRange.size
    unfold Size.mul
    simp [UInt64.mul_one, UInt64.div_one, Size.ofBytes]
  obtain ⟨updated, h_ok, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_ml, h_mwf,
      h_isInit, h_mget, h_mframe, h_prov, h_bytes, h_frame⟩ :=
    copyRepeatedly_initialized_spec source state sourceRange srcFinish destStart sourceRange.size ptrSize
      1 sameAllocation nonoverlapping srcBytes provCopy clearedProv finalProv
      srcStorage srcEnd srcNonzero srcMaskLen srcMaskWF srcInit srcSlice srcInBounds h_prepProv
      (by decide) h_mul1 (fun h => absurd h (by decide)) h_disjSame
      destStorage destMut destMaskLen destMaskWF destInBounds h_clearProv h_applyProv
  have h_flat1 : (List.replicate (1 : UInt64).toNat srcBytes.toList).flatten.toArray = srcBytes := by
    have h1 : (1 : UInt64).toNat = 1 := rfl
    simp [h1]
  rw [h_flat1] at h_bytes
  exact ⟨updated, h_ok, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_ml, h_mwf,
    h_isInit, h_mget, h_mframe, h_prov, h_bytes, h_frame⟩

end Miri.Memory.Allocation
