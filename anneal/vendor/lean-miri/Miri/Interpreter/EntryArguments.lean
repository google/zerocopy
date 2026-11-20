import Miri.Interpreter.MachineGCRoots
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.RawMemoryMachine

/-! eval.rs:390–471,641–710: actual immutable argument/argv/root-cell memory
and Windows command-line encoding. Compiler array-layout queries retain real
TyIds; projected indices execute the existing effectful canonical Place path. -/
namespace Miri.Interpreter.EntryArguments
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency

private def escaped : List Char → Nat → List Char
  | [],slashes => List.replicate (slashes*2) '\\'
  | '\\'::rest,slashes => escaped rest (slashes+1)
  | '"'::rest,slashes => List.replicate (slashes*2+1) '\\' ++ '"' :: escaped rest 0
  | char::rest,slashes => List.replicate slashes '\\' ++ char :: escaped rest 0
private def utf16 (chars : List Char) : Array UInt16 := Id.run do
  let mut result := #[]
  for char in chars do
    let value := char.toNat
    if value < 65536 then result := result.push (UInt16.ofNat value)
    else
      let value := value-65536
      result := (result.push (UInt16.ofNat (55296+value/1024))).push (UInt16.ofNat (56320+value%1024))
  return result

/-- Source initialization panics are explicit invalid-program results, never
host exceptions. Empty argv produces exactly one UTF-16 zero. -/
def windowsCommandLine (args : Array String) : Except StepError (Array UInt16) := do
  let some first := args[0]? | return #[0]
  if first.toList.contains '"' then throw (.invalidProgram "argv[0] cannot contain a doublequote")
  let mut chars := ['"'] ++ first.toList ++ ['"']
  for argument in args.toList.drop 1 do
    chars := chars ++ [' ']
    if argument.isEmpty then chars := chars ++ ['"','"']
    else if !(argument.toList.any fun char => char == '"' || char == '\t' || char == ' ') then
      chars := chars ++ argument.toList
    else chars := chars ++ ['"'] ++ escaped argument.toList 0 ++ ['"']
  if chars.contains '\x00' then throw (.invalidProgram "interior null in command line arguments")
  return (utf16 chars).push 0

structure Layouts where
  isize : LocalLayout
  u8 : LocalLayout
  u16 : LocalLayout
  u8Pointer : LocalLayout
  u8PointerPointer : LocalLayout
structure Arguments where
  argc : RvalueImmTy Provenance
  argv : RvalueImmTy Provenance

structure Hooks (K User AddressPayload AllocPayload C : Type) where
  addresses : FunctionPointers.AddressLens User AddressPayload
  /-- This is the already source-assembled allocation config. Its tail and
  root-address callback own extras and the persistent choice tape. -/
  allocation : PlaceMachine.AllocationConfig K (PointerMachine.User AddressPayload)
  arithmetic : PointerArithmetic
  access : PlaceMachine.AccessConfig K User
  place : PlaceProjectionHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
  layouts : Layouts
  /-- Ty::new_array(element,count) and layout_of in the actual typing environment. -/
  arrayLayout : C → TyId → UInt64 → MachineHooks.M K User LocalLayout
  entryPointers : User → MachineGCRoots.EntryPointers
  putEntryPointers : User → MachineGCRoots.EntryPointers → User
  windows : Bool
  isNoCore : MachineHooks.M K User Bool
  coreSentinelMirAvailable : MachineHooks.M K User Bool

private def liftResult (value : Except StepError A) : MachineHooks.M K User A :=
  match value with | .ok value => pure value | .error error => throw error

private def addressAction (lens : FunctionPointers.AddressLens User Payload)
    (action : PointerMachine.M K Payload A) : MachineHooks.M K User A := fun state =>
  let projected : PointerMachine.State K Payload := ⟨state.stack,{state.machine with user := lens.get state.machine.user}⟩
  match action projected with
  | .ok value result => .ok value ⟨result.stack,{result.machine with user := lens.put state.machine.user result.machine.user}⟩
  | .error error result => .error error ⟨result.stack,{result.machine with user := lens.put state.machine.user result.machine.user}⟩

private def allocate [DecidableEq K] (h : Hooks K User AP EP C) (layout : LocalLayout)
    (machineKind : K) : MachineHooks.M K User (MPlaceTy Provenance) := do
  unless layout.layout.isSized do throw (.invalidProgram "unsized argument allocation")
  let pointer ← addressAction h.addresses (ReallocationDriver.allocateConfigured h.allocation
    layout.layout.size layout.layout.align.abi (.machine machineKind) .Uninit)
  return ⟨⟨pointer.withOptionalProvenance,.none,none⟩,layout⟩

private def immutable [DecidableEq K] (place : MPlaceTy Provenance) : MachineHooks.M K User Unit := do
  let some provenance := place.mplace.ptr.provenance | throw (.invalidProgram "argument allocation lacks provenance")
  let some id := PointerProvenance.getAllocId provenance | throw (.invalidProgram "argument allocation lacks identity")
  let state ← get
  let some (_,entry) := state.machine.memory.live.find? (fun entry => entry.1 == id) |
    throw (.invalidProgram "argument allocation is not live")
  let memory ← liftResult (state.machine.memory.setLiveAllocation id (entry.allocation.withMutability .Not)
    |>.mapError fun error => .invalidProgram s!"mark_immutable: {reprStr error}")
  set {state with machine := {state.machine with memory}}

private def strictPointer (place : MPlaceTy Provenance) : Except StepError (Pointer Provenance) := do
  let some provenance := place.mplace.ptr.provenance | throw (.invalidProgram "allocated argument pointer lacks provenance")
  return ⟨place.mplace.ptr.offset,provenance⟩
private def write (h : Hooks K User AP EP C) (choice : C) (value : Immediate Provenance)
    (place : MPlaceTy Provenance) : MachineHooks.M K User Unit :=
  writePlaceImmediate h.place.place choice value ⟨.memory place.mplace,place.layout⟩
private def index (h : Hooks K User AP EP C) (choice : C) (place : MPlaceTy Provenance)
    (index : UInt64) : MachineHooks.M K User (MPlaceTy Provenance) := do
  let result ← PlaceDynamic.index h.place choice ⟨.memory place.mplace,place.layout⟩ index
  match result.ref with
  | .memory mplace => return ⟨mplace,result.layout⟩
  | .local .. => throw (.invalidProgram "memory array projection became a local")
private def setEntry (h : Hooks K User AP EP C)
    (f : MachineGCRoots.EntryPointers → MachineGCRoots.EntryPointers) : MachineHooks.M K User Unit :=
  modify fun state =>
    let user := h.putEntryPointers state.machine.user (f (h.entryPointers state.machine.user))
    {state with machine := {state.machine with user}}

/-- The exact source initialization order: all strings, argv array, argc cell,
argv cell, optional UTF-16 command line, then return typed argc/argv for the
captured main callback. Every byte/scalar write invokes real memory policies. -/
def setup [DecidableEq K] (h : Hooks K User AP EP C) (choice : C) (machineKind : K)
    (args : Array String) : MachineHooks.M K User Arguments := do
  unless ← h.isNoCore do
    unless ← h.coreSentinelMirAvailable do
      throw (.invalidProgram "sysroot lacks core::ascii::escape_default MIR")
  if args.size >= 2^63 then throw (.invalidProgram "argc does not fit source i64")
  let argc ← liftResult (Scalar.fromInt args.size h.layouts.isize.layout.size |>.mapError ScalarOps.scalarError)
  let mut pointers : Array (Immediate Provenance) := #[]
  for argument in args do
    let bytes := argument.toUTF8
    if bytes.size+1 >= 2^64 then throw (.invalidProgram "argument length overflow")
    let count := UInt64.ofNat (bytes.size+1)
    let layout ← h.arrayLayout choice h.layouts.u8.ty count
    let place ← allocate h layout machineKind
    let _ ← RawMemoryMachine.writeCString h.access h.arithmetic bytes place.mplace.ptr count
    immutable place
    let pointer ← liftResult (place.mplace.toRef h.access.runtime.base |>.mapError ScalarOps.immediateError)
    pointers := pointers.push pointer
  if pointers.size >= 2^64 then throw (.invalidProgram "argv length overflow")
  let layout ← h.arrayLayout choice h.layouts.u8Pointer.ty (UInt64.ofNat pointers.size)
  let argvPlace ← allocate h layout machineKind
  for i in [:pointers.size] do
    let some pointer := pointers[i]? | throw (.invalidProgram "argv index disappeared")
    write h choice pointer (← index h choice argvPlace (UInt64.ofNat i))
  immutable argvPlace
  let argcCell ← allocate h h.layouts.isize machineKind
  write h choice (.scalar argc) argcCell
  immutable argcCell
  let argcPointer ← liftResult (strictPointer argcCell)
  setEntry h fun entry => {entry with argc := some argcPointer}
  let argvCell ← allocate h h.layouts.u8PointerPointer machineKind
  let argvScalar ← liftResult (Scalar.fromMaybePointer h.access.runtime.base argvPlace.mplace.ptr |>.mapError ScalarOps.scalarError)
  write h choice (.scalar argvScalar) argvCell
  immutable argvCell
  let argvPointer ← liftResult (strictPointer argvCell)
  setEntry h fun entry => {entry with argv := some argvPointer}
  if h.windows then
    let command ← liftResult (windowsCommandLine args)
    if command.size >= 2^64 then throw (.invalidProgram "Windows command line length overflow")
    let layout ← h.arrayLayout choice h.layouts.u16.ty (UInt64.ofNat command.size)
    let place ← allocate h layout machineKind
    let pointer ← liftResult (strictPointer place)
    setEntry h fun entry => {entry with commandLine := some pointer}
    for i in [:command.size] do
      let some unit := command[i]? | throw (.invalidProgram "UTF-16 index disappeared")
      let scalar ← liftResult (Scalar.fromUInt (BitVec.ofNat 128 unit.toNat) h.layouts.u16.layout.size |>.mapError ScalarOps.scalarError)
      write h choice (.scalar scalar) (← index h choice place (UInt64.ofNat i))
    immutable place
  let argv ← liftResult (argvPlace.mplace.toRef h.access.runtime.base |>.mapError ScalarOps.immediateError)
  return ⟨⟨.scalar argc,h.layouts.isize⟩,⟨argv,h.layouts.u8PointerPointer⟩⟩

/-- Actual Miri source kind, without choosing ownership from a layout size. -/
def initializeMiri (h : Hooks MiriMemoryKind User AP EP C) (choice : C)
    (args : Array String) : MachineHooks.M MiriMemoryKind User Arguments :=
  setup h choice .machine args
end Miri.Interpreter.EntryArguments
