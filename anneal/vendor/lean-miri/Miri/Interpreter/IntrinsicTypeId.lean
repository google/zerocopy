import Miri.Interpreter.Rvalue
import Miri.Interpreter.ScalarOps

/-! Pinned intrinsics.rs write_type_id/read_type_id and memory.rs
get_ptr_type_id. TypeId hashes remain decorated with compiler-owned provenance;
integer equality alone cannot validate a forged TypeId. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR
structure IntrinsicTypeIdHooks (P S C V : Type) where
  target : TargetDataLayout
  hasErasableRegions : C → TyId → RvalueM S Bool
  typeHash : C → TyId → RvalueM S U128
  u128Layout : C → RvalueM S (TyAndLayout TyId)
  unitLayout : C → RvalueM S (TyAndLayout TyId)
  reserveTypeId : C → TyId → RvalueM S AllocId
  globalRootPointer : C → AllocId → Size → RvalueM S (Pointer P)
  resolvePointer : C → Pointer (Option P) → RvalueM S (AllocId × Size)
  globalTypeId : C → AllocId → RvalueM S (Option TyId)
  placeLayout : V → TyAndLayout TyId
  copyAllowTransmute : C → OpTy P → V → RvalueM S Unit
  projectFieldRead : C → OpTy P → Nat → RvalueM S (OpTy P)
  projectFieldWrite : C → V → Nat → RvalueM S V
  elementLayout : C → TyAndLayout TyId → RvalueM S (TyAndLayout TyId)
  offsetRead : C → OpTy P → Size → OffsetMode → TyAndLayout TyId → RvalueM S (OpTy P)
  offsetWrite : C → V → Size → OffsetMode → TyAndLayout TyId → RvalueM S V
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  readPlaceScalar : C → V → RvalueM S (Memory.Scalar P)
  writeScalar : C → Memory.Scalar P → V → RvalueM S Unit

namespace IntrinsicTypeId
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def liftResult (value : Except StepError A) : RvalueM S A :=
  match value with | .ok value => pure value | .error error => throw error
private def product (stride : Size) (count : UInt64) : RvalueM S Size :=
  liftResult (stride.mul count |>.mapError fun e => .invalidProgram (toString e))
private def arrayShape (layout : TyAndLayout TyId) : RvalueM S (Size × UInt64) :=
  match layout.layout.fields with
  | .Array stride count => pure (stride,count)
  | _ => invalid "TypeId field must be array-shaped"

/-- Source get_ptr_type_id checks the global allocation kind, retaining the
pointer offset as its hash fragment rather than requiring a zero offset. -/
def getPointerType [PointerProvenance P] (h : IntrinsicTypeIdHooks P S C V) (choice : C)
    (pointer : Pointer (Option P)) : RvalueM S (TyId × UInt64) := do
  let (id, offset) ← h.resolvePointer choice pointer
  let some ty ← h.globalTypeId choice id
    | throw (.undefinedBehavior "invalid TypeId: not all bytes carry type id metadata")
  pure (ty,offset.bytes)

def write [PointerProvenance P] (h : IntrinsicTypeIdHooks P S C V) (choice : C) (ty : TyId) (dest : V) : RvalueM S Unit := do
  if ← h.hasErasableRegions choice ty then invalid "TypeId type has erasable regions"
  let hash ← h.typeHash choice ty
  let layout ← h.u128Layout choice
  let scalar ← liftResult (Memory.Scalar.fromUInt hash layout.layout.size |>.mapError ScalarOps.scalarError)
  h.copyAllowTransmute choice ⟨.immediate (.scalar scalar),layout⟩ dest
  let id ← h.reserveTypeId choice ty
  let array ← h.projectFieldWrite choice dest 0
  let arrayLayout := h.placeLayout array
  let (stride,count) ← arrayShape arrayLayout
  let element ← h.elementLayout choice arrayLayout
  let endOffset ← product stride count
  let unit ← h.unitLayout choice
  let _ ← h.offsetWrite choice array endOffset .inbounds unit
  for index in [:count.toNat] do
    let offset ← product stride (UInt64.ofNat index)
    let element ← h.offsetWrite choice array offset .wrapping element
    let scalar ← h.readPlaceScalar choice element
    let fragment ← liftResult (scalar.toTargetUsize (Size.fromBits h.target.pointerWidth.bits) |>.mapError ScalarOps.scalarError)
    let pointer ← h.globalRootPointer choice id (Size.ofBytes fragment)
    h.writeScalar choice (.fromPointer h.target pointer) element

private def hashFragment (target : TargetDataLayout) (hash : U128) (index : Nat) : RvalueM S UInt64 := do
  let bits := target.pointerWidth.bits.toNat
  if (index+1)*bits > 128 then invalid "TypeId hash fragment index exceeds u128"
  let shift := match target.endian with | .little => index*bits | .big => 128-(index+1)*bits
  pure (UInt64.ofNat ((hash.toNat / 2^shift) % 2^bits))

def read [PointerProvenance P] (h : IntrinsicTypeIdHooks P S C V) (choice : C) (op : OpTy P) : RvalueM S TyId := do
  let array ← h.projectFieldRead choice op 0
  let (stride,count) ← arrayShape array.layout
  let element ← h.elementLayout choice array.layout
  let endOffset ← product stride count
  let unit ← h.unitLayout choice
  let _ ← h.offsetRead choice array endOffset .inbounds unit
  let mut remembered : Option (TyId × U128) := none
  for index in [:count.toNat] do
    let offset ← product stride (UInt64.ofNat index)
    let element ← h.offsetRead choice array offset .wrapping element
    let value ← h.readImmediate choice element
    let scalar ← liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
    let pointer ← liftResult (scalar.toPointer h.target |>.mapError ScalarOps.scalarError)
    let (ty,fragment) ← getPointerType h choice pointer
    let hash ← match remembered with
      | none => do
        let hash ← h.typeHash choice ty
        remembered := some (ty,hash)
        pure hash
      | some (oldTy,hash) => do
        if oldTy != ty then throw (.undefinedBehavior "invalid TypeId: bytes carry different type id metadata")
        pure hash
    let expected ← hashFragment h.target hash index
    if fragment != expected then throw (.undefinedBehavior "invalid TypeId: hash does not match metadata")
  let some (ty,_) := remembered | invalid "empty TypeId representation"
  pure ty
end IntrinsicTypeId
end Miri.Interpreter
