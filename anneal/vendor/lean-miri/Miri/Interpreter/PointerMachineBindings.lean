import Miri.Interpreter.PointerMachine
import Miri.Interpreter.Cast
import Miri.Interpreter.IntrinsicAtomic
import Miri.Memory.AllocationAccess
import Miri.Interpreter.Intrinsics

/-! Concrete dictionary wiring for canonical Miri pointer provenance. These
bindings retain the unrelated compiler, validity, memory and float leaves. -/
namespace Miri.Interpreter.PointerMachine
open Miri.ABI Miri.Memory Miri.MIR

private def liftResult (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Signed interval checks use canonical memory, preserving the zero-byte fast
path and concrete dangling provenance until liveness checking. -/
def checkAccessSigned (h : Hooks K U) (pointer : Pointer (Option Provenance))
    (size : Int64) (message : CheckInAllocMsg) : M K U Unit := do
  if size == 0 then return ()
  let resolved ← match pointer.provenance with
    | none => pure none
    | some provenance => ptrGetAlloc h (Pointer.new provenance pointer.offset) size
  let memory := (← get).machine.memory
  let resolver : PointerResolver Provenance Provenance := fun _ _ =>
    match resolved with
    | none => .error pointer.offset.bytes
    | some (id, offset) => .ok ⟨id, offset, pointer.provenance.getD .wildcard⟩
  match checkPtrAccessSigned h.arithmetic pointer size message resolver memory.getAllocInfo with
  | .ok () => pure ()
  | .error (.allocationLookup (.unavailable id)) =>
    throw (.callback s!"missing compiler allocation metadata: {reprStr id}")
  | .error (.malformedAlignment error) => throw (.invalidProgram s!"{reprStr error}")
  | .error (.pointerArithmetic error) => throw (.invalidProgram s!"{reprStr error}")
  | .error error => throw (.undefinedBehavior (toString error))

def offsetInbounds (h : Hooks K U) (pointer : Pointer (Option Provenance))
    (offset : Int64) : M K U (Pointer (Option Provenance)) := do
  checkAccessSigned h pointer offset .inboundsPointerArithmetic
  liftResult ((pointer.wrappingSignedOffset offset h.arithmetic).mapError
    fun error => h.classifyAddressError (.pointerArithmetic error))

/-- rustc's Offset arm precedes Miri's bitwise/comparison machine fallback.
Pointee layout and signedness are compiler facts; arithmetic is concrete. -/
def binary (h : Hooks K U) (target : TargetDataLayout)
    (ops : ScalarOpsHooks Provenance (State K U) C)
    (isRaw : C → TyId → M K U Bool)
    (usize : C → M K U (TyAndLayout TyId))
    (pointeeLayout : C → TyId → M K U (TyAndLayout TyId)) (choice : C)
    (op : BinOp) (left right : RvalueImmTy Provenance) : M K U (RvalueImmTy Provenance) := do
  if op != .Offset then
    return ← IntrinsicAtomic.pointerBinary target ops isRaw usize choice op left right
  let scalar ← liftResult (left.imm.toScalar.mapError ScalarOps.immediateError)
  let pointer ← liftResult (scalar.toPointer target |>.mapError ScalarOps.scalarError)
  let layout ← pointeeLayout choice left.layout.ty
  unless layout.layout.isSized && layout.layout.size.bytes.toNat < 2^63 do
    throw (.invalidProgram "pointer Offset requires sized pointee fitting i64")
  let stride ← liftResult (Memory.Scalar.fromInt (Int.ofNat layout.layout.size.bytes.toNat)
    right.layout.layout.size |>.mapError ScalarOps.scalarError)
  let multiplied ← ScalarOps.binary ops choice .MulWithOverflow right ⟨.scalar stride, right.layout⟩
  let (value, overflow) ← liftResult (multiplied.imm.toScalarPair.mapError ScalarOps.immediateError)
  if ← liftResult (overflow.toBool.mapError ScalarOps.scalarError) then
    throw (.undefinedBehavior "PointerArithOverflow")
  let offset ← liftResult (value.toTargetIsize h.arithmetic.pointerSize |>.mapError ScalarOps.scalarError)
  let signed ← liftResult (right.layout.layout.backendRepr.isSigned.mapError
    fun error => .invalidProgram s!"Offset backend representation: {reprStr error}")
  if !signed && offset.toInt < 0 then throw (.undefinedBehavior "PointerArithOverflow")
  let pointer ← offsetInbounds h pointer offset
  let result ← liftResult (Memory.Scalar.fromMaybePointer target pointer |>.mapError ScalarOps.scalarError)
  return ⟨.scalar result, left.layout⟩

def scalarOps (h : Hooks K U) (target : TargetDataLayout)
    (ops : ScalarOpsHooks Provenance (State K U) C)
    (isRaw : C → TyId → M K U Bool)
    (usize : C → M K U (TyAndLayout TyId))
    (pointeeLayout : C → TyId → M K U (TyAndLayout TyId)) :
    ScalarOpsHooks Provenance (State K U) C :=
  { ops with pointerBinary := binary h target ops isRaw usize pointeeLayout }

/-- Pointer-to-integer exposure preserves the scalar's actual address; only
provenance exposure is rebound here. Cast's width/sign conversion is unchanged. -/
def castHooks [DecidableEq K] (h : Hooks K U)
    (base : CastHooks Provenance (State K U) C V) :
    CastHooks Provenance (State K U) C V :=
  { base with
    exposeProvenance := fun _ provenance => exposeProvenance h provenance
    pointerFromExposedAddress := fun _ address => pointerFromExposedAddress h address }

/-- Memory's resolver distinguishes unresolved integer addresses from missing
semantics. Wildcard resolution is performed anew on every access. A concrete
pointer's TB tag and a wildcard marker survive in the resolved extra. -/
def resolvePointer (h : Hooks K U)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (state : State K U) (pointer : Pointer (Option Provenance)) (size : Int) :
    MachineHookResult (State K U) (Except UInt64 (ResolvedPointer Provenance)) := Id.run do
  if size < -(2^63 : Int) || size >= 2^63 then
    return ⟨state, .error "pointer resolution access size does not fit i64"⟩
  let some provenance := pointer.provenance
    | return ⟨state, .ok (.error pointer.offset.bytes)⟩
  let lookup : Miri.Memory.AllocAddresses.AddressLookupHooks := {
    sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size)
    isLive := fun id => some (memory.isAllocLive id) }
  match state.machine.user.addresses.ptrGetAlloc
      (Pointer.new provenance pointer.offset) (Int64.ofInt size) lookup h.arithmetic with
  | .error error => return ⟨state, .error s!"address resolver: {reprStr error}"⟩
  | .ok none => return ⟨state, .ok (.error pointer.offset.bytes)⟩
  | .ok (some (id, offset)) => return ⟨state, .ok (.ok ⟨id, offset, provenance⟩)⟩

/-- Actual AllocationAccess dictionary: all TB/race/sync physical access stages
remain in the supplied machine dictionary; only provenance resolution changes. -/
def allocationAccessHooks (h : Hooks K U)
    (base : AllocationAccessHooks Provenance Miri.TreeBorrows.BorrowTree K
      (State K U) Provenance) :
    AllocationAccessHooks Provenance Miri.TreeBorrows.BorrowTree K (State K U) Provenance :=
  { base with resolvePointer := resolvePointer h }

/-- Bind the already ported full ptr_offset_from pipeline to actual memory
resolution and inbounds checks. Errors inside the source deferred check are
returned as values so its two-direction error preference remains intact. -/
def intrinsicHooks (h : Hooks K U)
    (base : IntrinsicHooks Provenance (State K U) C V) :
    IntrinsicHooks Provenance (State K U) C V :=
  { base with
    tryAllocId := fun _ pointer => do
      match pointer.provenance with
      | none => return .error pointer.offset.bytes
      | some provenance =>
        match ← ptrGetAlloc h (Pointer.new provenance pointer.offset) 0 with
        | none => return .error pointer.offset.bytes
        | some result => return .ok result
    checkSignedAccess := fun _ pointer size => fun state =>
      match checkAccessSigned h pointer size .inboundsPointerArithmetic state with
      | .ok () state => .ok (.ok ()) state
      | .error error state => .ok (.error error) state }

/-- Symbolic promises override the concrete address check only when source
requests that mode and allocation kind. Canonical memory supplies liveness,
alignment and allocation kind; wildcard provenance is resolved per call. -/
def checkAlignment (h : Hooks K U) (symbolic enforce : Bool)
    (pointer : Pointer (Option Provenance)) (required : Align) : M K U Unit := do
  let requiredBytes ← liftResult (required.bytes.mapError fun error =>
    .invalidProgram s!"alignment metadata: {reprStr error}")
  let _ ← liftResult (Align.fromBytes requiredBytes |>.mapError fun error =>
    .invalidProgram s!"alignment metadata: {reprStr error}")
  if !enforce || requiredBytes == 1 then return ()
  let state ← get
  let resolution := resolvePointer h state.machine.memory state pointer 0
  let resolved ← match resolution.outcome with
    | .error message => throw (.callback message)
    | .ok value => pure value
  let mut override : Option Misalignment := none
  if let .ok resolved := resolved then
    let info ← match state.machine.memory.getAllocInfo resolved.allocId with
      | .error error => throw (.callback s!"alignment allocation metadata: {reprStr error}")
      | .ok info => pure info
    let promise := (state.machine.user.symbolicAlignment.find? fun entry =>
      entry.1 == resolved.allocId).map fun entry => (entry.2.1, entry.2.2)
    override ← liftResult ((symbolicAlignment symbolic info.kind info.align promise resolved.offset required).mapError
      fun error => .invalidProgram s!"alignment metadata: {reprStr error}")
  let resolver : PointerResolver Provenance Provenance := fun _ _ => resolved
  let result := checkPtrAlign pointer required enforce resolver state.machine.memory.getAllocInfo
    (fun _ _ _ _ _ => override)
  match result with
  | .ok () => pure ()
  | .error (.alignmentCheckFailed mismatch) => throw (.undefinedBehavior s!"AlignmentCheckFailed: {reprStr mismatch}")
  | .error error => throw (.invalidProgram s!"alignment check: {reprStr error}")

end Miri.Interpreter.PointerMachine
