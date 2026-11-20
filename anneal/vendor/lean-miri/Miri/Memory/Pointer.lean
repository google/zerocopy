import Miri.ABI.Size
import Miri.Memory.Identity

/-!
The generic engine pointer from pinned rustc `mir/interpret/pointer.rs` and
the concrete Miri provenance from `machine.rs` are kept separate. In Miri the
offset field is an absolute address; with CTFE provenance it is relative.
None of these constructors or wrapping operations establishes dereference
validity, liveness, alignment, permission, or initialization.
-/

namespace Miri.Memory

open Miri.ABI

structure Pointer (Prov : Type u) where
  offset : Size
  provenance : Prov
  deriving DecidableEq, Repr

/-- Errors corresponding to source assertion/try_into failures, not UB. -/
inductive PointerError where
  | sourceSizeError (reason : SizeError)
  | unsignedConversionOverflow
  | signedConversionOverflow
  | relativeProvenanceHasNoAbsoluteAddress
  deriving DecidableEq, Repr

/-- Target-size operations from `PointerArithmetic`. Assertions and narrowing
conversion failures remain explicit. No target triple is selected here. -/
structure PointerArithmetic where
  pointerSize : Size
  deriving DecidableEq, Repr

namespace PointerArithmetic

private def sizeResult (result : Except SizeError α) : Except PointerError α :=
  result.mapError .sourceSizeError

private def toUInt64Checked (value : U128) : Except PointerError UInt64 :=
  if value.toNat < 2 ^ 64 then .ok (UInt64.ofNat value.toNat)
  else .error .unsignedConversionOverflow

private def toInt64Checked (value : Int) : Except PointerError Int64 :=
  if -(2 ^ 63 : Int) ≤ value ∧ value < (2 ^ 63 : Int) then .ok (Int64.ofInt value)
  else .error .signedConversionOverflow

def targetUsizeMax (cx : PointerArithmetic) : Except PointerError UInt64 := do
  toUInt64Checked (← sizeResult cx.pointerSize.unsignedIntMax)

def truncateToTargetUsize (cx : PointerArithmetic) (value : UInt64) :
    Except PointerError UInt64 := do
  toUInt64Checked (← sizeResult (cx.pointerSize.truncate (BitVec.ofNat 128 value.toNat)))

def signExtendToTargetIsize (cx : PointerArithmetic) (value : UInt64) :
    Except PointerError Int64 := do
  toInt64Checked (← sizeResult (cx.pointerSize.signExtend (BitVec.ofNat 128 value.toNat)))

def targetIsizeMax (cx : PointerArithmetic) : Except PointerError Int64 := do
  toInt64Checked (← sizeResult cx.pointerSize.signedIntMax)

def targetIsizeMin (cx : PointerArithmetic) : Except PointerError Int64 := do
  toInt64Checked (← sizeResult cx.pointerSize.signedIntMin)

/-- Pinned PointerArithmetic::max_size_of_val, independent of the ABI
object-size bound (which is smaller for 64-bit LLVM layouts). -/
def maxSizeOfVal (cx : PointerArithmetic) : Except PointerError Size := do
  let maximum ← cx.targetIsizeMax
  pure (Size.ofBytes (UInt64.ofNat maximum.toInt.toNat))

end PointerArithmetic

namespace Pointer

def new (provenance : Prov) (offset : Size) : Pointer Prov := ⟨offset, provenance⟩

def intoRawParts (ptr : Pointer Prov) : Prov × Size := (ptr.provenance, ptr.offset)

def mapProvenance (ptr : Pointer Prov) (f : Prov → Prov) : Pointer Prov :=
  { ptr with provenance := f ptr.provenance }

def withOptionalProvenance (ptr : Pointer Prov) : Pointer (Option Prov) :=
  ⟨ptr.offset, some ptr.provenance⟩

def withoutProvenance (addr : UInt64) : Pointer (Option Prov) :=
  ⟨Size.ofBytes addr, none⟩

def null : Pointer (Option Prov) := withoutProvenance 0

/-- Rust `Result<Pointer<Prov>, Size>`: an address without provenance goes
through the error branch, not a fabricated allocation. -/
def intoPointerOrAddr (ptr : Pointer (Option Prov)) : Except Size (Pointer Prov) :=
  match ptr.provenance with
  | some prov => .ok (new prov ptr.offset)
  | none => .error ptr.offset

/-- Source `addr` assertion depends on the provenance representation. -/
def addr [PointerProvenance Prov] (ptr : Pointer (Option Prov)) : Except PointerError Size :=
  if PointerProvenance.offsetIsAddr (Prov := Prov) then .ok ptr.offset
  else .error .relativeProvenanceHasNoAbsoluteAddress

/-- Source wraps u64 addition before truncating to the target pointer size. -/
def wrappingOffset (ptr : Pointer Prov) (offset : Size) (cx : PointerArithmetic) :
    Except PointerError (Pointer Prov) := do
  let result ← cx.truncateToTargetUsize (ptr.offset.bytes + offset.bytes)
  return { ptr with offset := Size.ofBytes result }

def wrappingSignedOffset (ptr : Pointer Prov) (offset : Int64) (cx : PointerArithmetic) :
    Except PointerError (Pointer Prov) :=
  ptr.wrappingOffset (Size.ofBytes offset.toUInt64) cx

theorem map_preserves_offset (ptr : Pointer Prov) (f : Prov → Prov) :
    (ptr.mapProvenance f).offset = ptr.offset := rfl

theorem no_provenance_is_address (value : UInt64) :
    (withoutProvenance (Prov := Prov) value).intoPointerOrAddr =
      .error (Size.ofBytes value) := rfl

theorem wrappingOffset_preserves_provenance (ptr : Pointer Prov) (offset : Size)
    (cx : PointerArithmetic) (next : Pointer Prov)
    (h : ptr.wrappingOffset offset cx = .ok next) :
    next.provenance = ptr.provenance := by
  unfold wrappingOffset at h
  cases heq : cx.truncateToTargetUsize (ptr.offset.bytes + offset.bytes) with
  | error reason =>
      rw [heq] at h
      contradiction
  | ok value =>
      simp [heq] at h
      cases h
      rfl

end Pointer

abbrev MiriPointer := Pointer (Option Provenance)
abbrev StrictPointer := Pointer Provenance

end Miri.Memory
