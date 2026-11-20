import Miri.Interpreter.Rvalue
import Miri.Interpreter.ScalarOps

/-! C-varargs pipelines and compatibility recursion from pinned intrinsics.rs,
with memory.rs's symbolic VaList allocation lifecycle and partial updates. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR
inductive VaTypeInfo where
  | signedInteger (kind : IntegerKind)
  | unsignedInteger (kind : IntegerKind)
  | pointer (pointee : TyId)
  | other
  deriving DecidableEq, Repr
inductive VarArgCompatible where
  | compatible | incompatible | castInteger (sourceSigned : Bool)
  deriving DecidableEq, Repr
structure IntrinsicVarArgsHooks (P S C V : Type) where
  getLists : S → Array (AllocId × List V)
  setLists : S → Array (AllocId × List V) → S
  markDead : S → AllocId → Size → Align → S
  reserveAllocId : C → RvalueM S AllocId
  globalRootPointer : C → AllocId → RvalueM S (Pointer (Option P))
  resolvePointer : C → Pointer (Option P) → RvalueM S (AllocId × Size)
  destLayout : V → TyAndLayout TyId
  layoutOf : C → TyId → RvalueM S (TyAndLayout TyId)
  typeInfo : C → TyId → RvalueM S VaTypeInfo
  identicalCTypes : C → TyId → TyId → RvalueM S Bool
  isCVoid : C → TyId → RvalueM S Bool
  vaListFields : C → TyId → RvalueM S (Array TyId)
  isRawPointer : C → TyId → RvalueM S Bool
  projectField : C → V → Nat → RvalueM S V
  derefPointer : C → OpTy P → RvalueM S V
  placePointer : V → Except StepError (Pointer (Option P))
  readPointer : C → V → RvalueM S (Pointer (Option P))
  readScalar : C → V → RvalueM S (Memory.Scalar P)
  writePointer : C → Pointer (Option P) → V → RvalueM S Unit
  forceAllocation : C → V → RvalueM S V
  writeBytesPointer : C → Pointer (Option P) → UInt8 → Size → RvalueM S Unit
  copyAllowTransmute : C → V → V → RvalueM S Unit

namespace IntrinsicVarArgs
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def ub (message : String) : RvalueM S A := throw (.undefinedBehavior message)
private def liftResult (value : Except StepError A) : RvalueM S A :=
  match value with | .ok value => pure value | .error error => throw error

/-- First raw-pointer field of the target-specific VaListImpl after unwrapping
its outer field. Compiler field metadata is required and never guessed. -/
def keyField (h : IntrinsicVarArgsHooks P S C V) (choice : C) (place : V) : RvalueM S V := do
  let inner ← h.projectField choice place 0
  let fields ← h.vaListFields choice (h.destLayout inner).ty
  for index in [:fields.size] do
    let some ty := fields[index]? | invalid "VaList field index out of bounds"
    if ← h.isRawPointer choice ty then return (← h.projectField choice inner index)
  invalid "VaListImpl has no raw pointer field"

private def resolve (h : IntrinsicVarArgsHooks P S C V) (choice : C) (pointer : Pointer (Option P)) : RvalueM S AllocId := do
  let (id,offset) ← h.resolvePointer choice pointer
  if offset != Size.ZERO then ub "InvalidVaListPointer"
  pure id

def getList (h : IntrinsicVarArgsHooks P S C V) (choice : C) (pointer : Pointer (Option P)) : RvalueM S (List V) := do
  let id ← resolve h choice pointer
  let entries := h.getLists (← get)
  let some entry := entries.find? (fun entry => entry.1 == id) | ub "InvalidVaListPointer"
  pure entry.2

/-- Source swap_remove and dead_alloc_map update occur before caller validation
or copying of a va_arg value. Errors retain this invalidation. -/
def deallocateList (h : IntrinsicVarArgsHooks P S C V) (choice : C) (pointer : Pointer (Option P)) : RvalueM S (List V) := do
  let id ← resolve h choice pointer
  let state ← get
  let entries := h.getLists state
  let some index := entries.findIdx? (fun entry => entry.1 == id) | ub "InvalidVaListPointer"
  let some entry := entries[index]? | invalid "VaList map index invalid"
  let some last := entries.back? | invalid "VaList map unexpectedly empty"
  let entries := (entries.setIfInBounds index last).pop
  let state := h.setLists state entries
  set (h.markDead state id Size.ZERO Align.ONE)
  pure entry.2

/-- Map insertion precedes global-root pointer creation, preserving the source
partial update even when the compiler/machine root-pointer query is unknown. -/
def createList (h : IntrinsicVarArgsHooks P S C V) (choice : C) (values : List V) : RvalueM S (Pointer (Option P)) := do
  let id ← h.reserveAllocId choice
  let state ← get
  let entries := h.getLists state
  let old := entries.findIdx? (fun entry => entry.1 == id)
  let entries := match old with
    | some index => entries.setIfInBounds index (id,values)
    | none => entries.push (id,values)
  set (h.setLists state entries)
  if old.isSome then invalid "reserved VaList allocation already exists"
  h.globalRootPointer choice id

private def cChar : VaTypeInfo → Bool
  | .signedInteger .i8 | .unsignedInteger .u8 => true | _ => false

/-- Exact source compatibility rules, with compiler C-type identity before
layout queries. Pointer target signedness differences require no value read. -/
def compatibleTypes (h : IntrinsicVarArgsHooks P S C V) (choice : C) (fuel : Nat)
    (caller callee : TyId) : RvalueM S VarArgCompatible := do
  if ← h.identicalCTypes choice caller callee then return .compatible
  match fuel with
  | 0 => throw (.resourceExhaustion "C variadic compatibility recursion fuel")
  | fuel + 1 =>
    let callerLayout ← h.layoutOf choice caller
    let calleeLayout ← h.layoutOf choice callee
    if callerLayout.layout.size != calleeLayout.layout.size then return .incompatible
    let callerKind ← h.typeInfo choice caller
    let calleeKind ← h.typeInfo choice callee
    match callerKind, calleeKind with
    | .signedInteger _, .signedInteger _ | .unsignedInteger _, .unsignedInteger _ => pure .compatible
    | .pointer a, .pointer b =>
      if ← h.isCVoid choice a then
        if cChar (← h.typeInfo choice b) then return .compatible
      if ← h.isCVoid choice b then
        if cChar (← h.typeInfo choice a) then return .compatible
      match ← compatibleTypes h choice fuel a b with
      | .incompatible => pure .incompatible
      | .compatible | .castInteger _ => pure .compatible
    | .signedInteger _, .unsignedInteger _ => pure (.castInteger true)
    | .unsignedInteger _, .signedInteger _ => pure (.castInteger false)
    | _, _ => pure .incompatible

def validateArgument [PointerProvenance P] (h : IntrinsicVarArgsHooks P S C V) (choice : C)
    (fuel : Nat) (source : V) (target : TyAndLayout TyId) : RvalueM S Unit := do
  let sourceLayout := h.destLayout source
  match ← compatibleTypes h choice fuel sourceLayout.ty target.ty with
  | .compatible => pure ()
  | .incompatible => ub "va_arg type mismatch"
  | .castInteger _ =>
    let value ← h.readScalar choice source
    let integer ← liftResult (value.toInt sourceLayout.layout.size |>.mapError ScalarOps.scalarError)
    if integer < 0 then ub "va_arg value cannot be represented in target integer type"

def copy (h : IntrinsicVarArgsHooks P S C V) (choice : C) (source : OpTy P) (dest : V) : RvalueM S Unit := do
  let source ← h.derefPointer choice source
  let key ← keyField h choice source
  let key ← h.readPointer choice key
  let values ← getList h choice key
  let copyKey ← createList h choice values
  let dest ← h.forceAllocation choice dest
  let pointer ← liftResult (h.placePointer dest)
  h.writeBytesPointer choice pointer 0 (h.destLayout dest).layout.size
  let key ← keyField h choice dest
  h.writePointer choice copyKey key

def finish (h : IntrinsicVarArgsHooks P S C V) (choice : C) (source : OpTy P) : RvalueM S Unit := do
  let source ← h.derefPointer choice source
  let key ← keyField h choice source
  let key ← h.readPointer choice key
  let _ ← deallocateList h choice key
  pure ()

def next [PointerProvenance P] (h : IntrinsicVarArgsHooks P S C V) (choice : C) (fuel : Nat)
    (source : OpTy P) (dest : V) : RvalueM S Unit := do
  let source ← h.derefPointer choice source
  let keyPlace ← keyField h choice source
  let key ← h.readPointer choice keyPlace
  let values ← deallocateList h choice key
  let value :: remaining := values | ub "VaArgOutOfBounds"
  validateArgument h choice fuel value (h.destLayout dest)
  h.copyAllowTransmute choice value dest
  let newKey ← createList h choice remaining
  h.writePointer choice newKey keyPlace
end IntrinsicVarArgs
end Miri.Interpreter
