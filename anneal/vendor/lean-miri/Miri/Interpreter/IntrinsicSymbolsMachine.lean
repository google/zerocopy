import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.OperandMachine
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.IntrinsicTypeId
import Miri.Interpreter.IntrinsicVectorMachine
import Miri.Interpreter.IntrinsicVarArgs

/-! Actual memory.rs TypeId globals and va_list_map. The maps start empty;
allocation IDs come from the same MemoryState reserve supply as every other
allocation. No Rust memory is allocated for symbolic TypeId/VaList entries.
provenance_gc.rs::VisitProvenance(MiriInterpCx) visits alloc_map and machine,
not rustc memory.va_list_map: these maps deliberately add no GC roots. -/
namespace Miri.Interpreter.IntrinsicSymbolsMachine
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (M State FrameExtra)
structure Registry where
  typeIds : Array (AllocId × TyId)
  vaLists : Array (AllocId × List (RuntimePlace Provenance))
def Registry.empty : Registry := ⟨#[],#[]⟩
structure Access (U : Type) where
  get : U → Registry
  put : U → Registry → U

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def reserve : M K U AllocId := do
  let state ← get
  let (memory,result) := state.machine.memory.reserveAllocId
  set {state with machine := {state.machine with memory}}
  match result with
  | .ok id => pure id
  | .error error => throw (.resourceExhaustion s!"symbolic allocation ID: {reprStr error}")

def reserveTypeId (registry : Access U) (ty : TyId) : M K U AllocId := do
  if let some (id,_) := (registry.get (← get).machine.user).typeIds.find? (·.2 == ty) then return id
  if (← get).machine.memory.sourceAllocIdWorldActive then
    throw (.unsupported "source TypeId AllocId key is not captured by the prepared raw-world profile")
  let id ← reserve
  modify fun state =>
    let entries := registry.get state.machine.user
    {state with machine := {state.machine with
      memory := MemoryState.pushGlobal state.machine.memory ⟨id,.typeId,.ZERO,.ONE,.Not,some .typeId⟩
      user := registry.put state.machine.user {entries with typeIds := entries.typeIds.push (id,ty)}}}
  pure id

def globalTypeId (registry : Access U) (imported : AllocId → M K U (Option TyId))
    (id : AllocId) : M K U (Option TyId) := do
  let state ← get
  let some info := state.machine.memory.findGlobal? id | return none
  if info.kind != .typeId then return none
  if let some (_,ty) := (registry.get state.machine.user).typeIds.find? (·.1 == id) then return some ty
  imported id

private def pointer (place : RuntimePlace Provenance) : Except StepError (Pointer (Option Provenance)) :=
  match place.ref with
  | .memory memory => .ok memory.ptr
  | .local .. => .error (.invalidProgram "symbolic intrinsic requires allocated memory place")
private def scalar [DecidableEq K] (access : PlaceMachine.AccessConfig K U) (operand : OpTy Provenance) :
    M K U (Scalar Provenance) := do
  lift ((← PlaceMachine.readImmediate access operand).imm.toScalar.mapError ScalarOps.immediateError)
private def offset (operands : OperandMachine.Hooks K U C) (c : C) (base : OpTy Provenance)
    (amount : Size) (mode : OffsetMode) (layout : LocalLayout) : M K U (OpTy Provenance) := do
  match base.op with
  | .indirect memory =>
    let value ← PlaceDynamic.offsetWithMeta operands.projection c ⟨.memory memory,base.layout⟩ amount mode .none layout
    let .memory memory := value.ref | throw (.invalidProgram "indirect offset returned local")
    pure ⟨.indirect memory,layout⟩
  | .immediate _ =>
    match base.offsetWithMeta (← operands.compiler.projection c) amount mode .none layout with
    | .ok value => pure value
    | .error error => throw (IntrinsicVectorMachine.projectionError error)

structure TypeIdLeaves (K U C : Type) where
  hasErasableRegions : C → TyId → M K U Bool
  typeHash : C → TyId → M K U U128
  u128Layout : C → M K U LocalLayout
  unitLayout : C → M K U LocalLayout
  importedTypeId : AllocId → M K U (Option TyId)

/-- Root-pointer tag/address effects execute before the hash-fragment offset
is restored. TypeId allocations have source special address zero. -/
def typeId [DecidableEq K] (leaves : TypeIdLeaves K U C) (registry : Access U)
    (access : PlaceMachine.AccessConfig K U) (functions : FunctionPointers.Hooks K U O)
    (operands : OperandMachine.Hooks K U C)
    (copy : PlaceCopyHooks Provenance (State K U) C) :
    IntrinsicTypeIdHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let places := operands.projection.place
  {target := access.runtime.base
   hasErasableRegions := leaves.hasErasableRegions
   typeHash := leaves.typeHash
   u128Layout := leaves.u128Layout
   unitLayout := leaves.unitLayout
   reserveTypeId := fun _ => reserveTypeId registry
   globalRootPointer := fun _ id fragment => do
     let ptr ← FunctionPointers.rootPointer functions id
     pure {ptr with offset := Size.ofBytes (ptr.offset.bytes + fragment.bytes)}
   resolvePointer := fun _ ptr => do
     let some provenance := ptr.provenance | throw (.undefinedBehavior "invalid TypeId pointer")
     let some pair ← functions.ptrGetAlloc (Pointer.new provenance ptr.offset) | throw (.undefinedBehavior "invalid TypeId pointer")
     pure pair
   globalTypeId := fun _ => globalTypeId registry leaves.importedTypeId
   placeLayout := RuntimePlace.layout
   copyAllowTransmute := fun c source dest => copyRuntimePlace places copy c source dest true
   projectFieldRead := OperandMachine.field operands
   projectFieldWrite := PlaceDynamic.field operands.projection
   elementLayout := fun c layout => operands.projection.field c layout 0
   offsetRead := offset operands
   offsetWrite := fun c base amount mode layout => PlaceDynamic.offsetWithMeta operands.projection c base amount mode .none layout
   readImmediate := fun _ => PlaceMachine.readImmediate access
   readPlaceScalar := fun c place => do scalar access (← placeToOp places c place)
   writeScalar := fun c value place => writePlaceImmediate places c (.scalar value) place}

structure VarArgsLeaves (K U C : Type) where
  layoutOf : C → TyId → M K U LocalLayout
  typeInfo : C → TyId → M K U VaTypeInfo
  identicalCTypes : C → TyId → TyId → M K U Bool
  isCVoid : C → TyId → M K U Bool
  vaListFields : C → TyId → M K U (Array TyId)
  isRawPointer : C → TyId → M K U Bool

def varArgs [DecidableEq K] (leaves : VarArgsLeaves K U C) (registry : Access U)
    (access : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (functions : FunctionPointers.Hooks K U O) (operands : OperandMachine.Hooks K U C)
    (copy : PlaceCopyHooks Provenance (State K U) C) :
    IntrinsicVarArgsHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let places := operands.projection.place
  {getLists := fun state => (registry.get state.machine.user).vaLists
   setLists := fun state lists => {state with machine := {state.machine with
     user := registry.put state.machine.user {registry.get state.machine.user with vaLists := lists}
     memory := MemoryState.setVaListIds state.machine.memory (lists.map (·.1))}}
   markDead := fun state id size align => {state with machine := {state.machine with memory :=
     {state.machine.memory with dead := (state.machine.memory.dead.filter (·.allocId != id)).push ⟨id,size,align⟩}}}
   reserveAllocId := fun _ => reserve
   globalRootPointer := fun _ id => do return (← FunctionPointers.rootPointer functions id).withOptionalProvenance
   resolvePointer := fun _ ptr => do
     let some provenance := ptr.provenance | throw (.undefinedBehavior "invalid VaList pointer")
     let some pair ← functions.ptrGetAlloc (Pointer.new provenance ptr.offset) | throw (.undefinedBehavior "invalid VaList pointer")
     pure pair
   destLayout := RuntimePlace.layout
   layoutOf := leaves.layoutOf
   typeInfo := leaves.typeInfo
   identicalCTypes := leaves.identicalCTypes
   isCVoid := leaves.isCVoid
   vaListFields := leaves.vaListFields
   isRawPointer := leaves.isRawPointer
   projectField := PlaceDynamic.field operands.projection
   derefPointer := fun c op => do
     let value ← operands.dereference c op
     pure ⟨.memory value.mplace,value.layout⟩
   placePointer := pointer
   readPointer := fun c place => do
     lift ((← scalar access (← placeToOp places c place)).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
   readScalar := fun c place => do scalar access (← placeToOp places c place)
   writePointer := fun c ptr place => do
     let value ← lift (Scalar.fromMaybePointer access.runtime.base ptr |>.mapError ScalarOps.scalarError)
     writePlaceImmediate places c (.scalar value) place
   forceAllocation := fun c place => do
     let value ← forceAllocation places c place
     pure ⟨.memory value.mplace,value.layout⟩
   writeBytesPointer := fun _ ptr byte size => RawMemoryMachine.writeRepeatedByte access arithmetic ptr byte size.bytes
   copyAllowTransmute := fun c source dest => do copyRuntimePlace places copy c (← placeToOp places c source) dest true}
end Miri.Interpreter.IntrinsicSymbolsMachine
