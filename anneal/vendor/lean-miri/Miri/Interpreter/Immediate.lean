import Miri.Memory.Scalar

/-! The self-contained value representation and pointer metadata from the
pinned interpreter's `operand.rs` and `place.rs`. Layout/ABI validation is a
separate caller obligation; an immediate alone is not a typed Rust value. -/
namespace Miri.Interpreter

open Miri.Memory Miri.ABI

inductive MemPlaceMeta (Prov : Type) where
  | metadata (value : Scalar Prov)
  | none
  deriving DecidableEq, Repr

inductive Immediate (Prov : Type) where
  | scalar (value : Scalar Prov)
  | scalarPair (first second : Scalar Prov)
  | uninit
  deriving DecidableEq, Repr

inductive ImmediateError where
  | scalar (reason : ScalarError)
  | expectedScalar
  | expectedScalarPair
  | unexpectedUninit
  | expectedInteger
  | expectedMetadata
  deriving DecidableEq, Repr

def MemPlaceMeta.unwrapMeta : MemPlaceMeta Prov → Except ImmediateError (Scalar Prov)
  | .metadata value => .ok value
  | .none => .error .expectedMetadata

def MemPlaceMeta.hasMeta : MemPlaceMeta Prov → Bool
  | .metadata _ => true
  | .none => false

namespace Immediate

def newPointerWithMeta (pointer : Pointer (Option Prov)) (metadata : MemPlaceMeta Prov)
    (layout : TargetDataLayout) : Except ImmediateError (Immediate Prov) := do
  let scalar ← Scalar.fromMaybePointer layout pointer |>.mapError .scalar
  return match metadata with
    | .none => .scalar scalar
    | .metadata value => .scalarPair scalar value

def newSlice (pointer : Pointer (Option Prov)) (length : UInt64) (layout : TargetDataLayout) :
    Except ImmediateError (Immediate Prov) := do
  let scalar ← Scalar.fromMaybePointer layout pointer |>.mapError .scalar
  let length ← Scalar.fromUInt (BitVec.ofNat 128 length.toNat) (Size.fromBits layout.pointerWidth.bits)
    |>.mapError .scalar
  return .scalarPair scalar length

def newDynTrait (pointer vtable : Pointer (Option Prov)) (layout : TargetDataLayout) :
    Except ImmediateError (Immediate Prov) := do
  let scalar ← Scalar.fromMaybePointer layout pointer |>.mapError .scalar
  let vtable ← Scalar.fromMaybePointer layout vtable |>.mapError .scalar
  return .scalarPair scalar vtable

def toScalar : Immediate Prov → Except ImmediateError (Scalar Prov)
  | .scalar value => .ok value
  | .scalarPair .. => .error .expectedScalar
  | .uninit => .error .unexpectedUninit

def toScalarInt [PointerProvenance Prov] (self : Immediate Prov) :
    Except ImmediateError ScalarInt := do
  let scalar ← self.toScalar
  match ← scalar.tryToScalarInt |>.mapError .scalar with
  | .integer value => return value
  | .erasedPointer .. => throw .expectedInteger

def toScalarPair : Immediate Prov → Except ImmediateError (Scalar Prov × Scalar Prov)
  | .scalarPair first second => .ok (first, second)
  | .scalar _ => .error .expectedScalarPair
  | .uninit => .error .unexpectedUninit

def toScalarAndMeta : Immediate Prov → Except ImmediateError (Scalar Prov × MemPlaceMeta Prov)
  | .scalarPair first second => .ok (first, .metadata second)
  | .scalar value => .ok (value, .none)
  | .uninit => .error .unexpectedUninit

def hasProvenance : Immediate Prov → Bool
  | .scalar value => value.isPointer
  | .scalarPair first second => first.isPointer || second.isPointer
  | .uninit => false

/-- Preserve source in-place sequencing: if the second component fails to
clear its provenance, the first component remains converted. -/
def clearProvenance [PointerProvenance Prov] : EStateM ScalarError (Immediate Prov) Unit := do
  match ← EStateM.get with
  | .scalar value =>
    match value.clearProvenance with
    | .ok next => EStateM.set (.scalar next)
    | .error reason => throw reason
  | .scalarPair first second =>
    let first ← match first.clearProvenance with
      | .ok next => pure next
      | .error reason => throw reason
    EStateM.set (.scalarPair first second)
    let second ← match second.clearProvenance with
      | .ok next => pure next
      | .error reason => throw reason
    EStateM.set (.scalarPair first second)
  | .uninit => pure ()

theorem scalar_to_scalar (value : Scalar Prov) : toScalar (.scalar value) = .ok value := rfl

theorem uninit_has_no_provenance : hasProvenance (.uninit : Immediate Prov) = false := rfl

end Immediate
end Miri.Interpreter
