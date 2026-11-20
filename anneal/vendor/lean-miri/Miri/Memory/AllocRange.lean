import Miri.ABI.Size

/-! Checked byte ranges used by the rustc allocation interpreter. -/

namespace Miri.Memory
open Miri.ABI

/-- Failures that upstream represents as a checked-size error or a panic. -/
inductive MemoryError where
  | sizeError (error : SizeError)
  | sizeFromNatOverflow (attempted : Nat)
  | blockCapacityTooSmall (logicalBytes capacityBytes : Nat)
  | blockIndexOutOfBounds (index available : Nat)
  | rangeOutOfBounds (finish length : Size)
  | emptyCopyRange
  | invalidCopyEncoding
  | invalidChunkIterator (start finish : Size)
  | accessOutsideBounds (outerStart outerFinish subStart subFinish : Size)
  deriving DecidableEq, Repr

instance : ToString MemoryError where
  toString
    | .sizeError error => toString error
    | .sizeFromNatOverflow attempted =>
        s!"Size conversion: {attempted} bytes does not fit in u64"
    | .blockCapacityTooSmall logical capacity =>
        s!"InitMask block capacity {capacity} is smaller than logical length {logical}"
    | .blockIndexOutOfBounds index available =>
        s!"InitMask block index {index} is outside {available} materialized blocks"
    | .rangeOutOfBounds finish length =>
        s!"range ends at {finish.bytes}, beyond mask length {length.bytes}"
    | .emptyCopyRange => "InitMask::prepare_copy requires a nonempty range"
    | .invalidCopyEncoding => "InitMask copy encoding has no positive-length runs"
    | .invalidChunkIterator start finish =>
        s!"invalid InitChunkIter state [{start.bytes}..{finish.bytes}]"
    | .accessOutsideBounds outerStart outerFinish subStart subFinish =>
        s!"subrange [{subStart.bytes}..{subFinish.bytes}] escapes [{outerStart.bytes}..{outerFinish.bytes}]"

/-- An access interval represented by start offset and byte length. -/
structure AllocRange where
  start : Size
  size : Size
  deriving DecidableEq, Repr

/-- Construct an access range from its start and byte size. -/
def allocRange (start size : Size) : AllocRange := ⟨start, size⟩

/-- Checked exclusive end offset, mirroring `AllocRange::end` and `Size` addition. -/
def AllocRange.end (range : AllocRange) : Except MemoryError Size :=
  (Size.add range.start range.size).mapError MemoryError.sizeError

/-- Descriptive alias for the checked exclusive end offset. -/
def AllocRange.endExclusive (range : AllocRange) : Except MemoryError Size :=
  range.end

/-- Checked construction from two endpoints, mirroring Size subtraction. -/
def AllocRange.fromEndpoints (start finish : Size) : Except MemoryError AllocRange := do
  let size ← (Size.sub finish start).mapError MemoryError.sizeError
  return ⟨start, size⟩

/-- Return a subrange relative to this interval or report the source assertion failure. -/
def AllocRange.subrange (range subrange : AllocRange) : Except MemoryError AllocRange := do
  let subStart ← (Size.add range.start subrange.start).mapError MemoryError.sizeError
  let result := allocRange subStart subrange.size
  let resultEnd ← result.endExclusive
  let outerEnd ← range.endExclusive
  if resultEnd.bytes ≤ outerEnd.bytes then
    return result
  else
    throw (.accessOutsideBounds range.start outerEnd subStart resultEnd)

end Miri.Memory
