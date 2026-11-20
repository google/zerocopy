import Miri.Interpreter.EventFd
import Miri.Interpreter.ReadinessMachine
import Miri.Interpreter.PointerPlaceMachine

/-! Event objects share the actual FD ownership/readiness registry. Tags carry
only canonical FD identity; counter/clock/queues have one authoritative store. -/
namespace Miri.Interpreter.EventFdMachine
open Miri.ABI Miri.Memory Miri.Concurrency Files
abbrev Ref (H D O : Type) := Files.Ref (Description H D O)
structure Store (U O : Type) where
  get : U → Array (FdId × EventFd.Event)
  put : Array (FdId × EventFd.Event) → U → U
  tag : FdId → O
  untag : O → Option FdId
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def eventId (store : Store U O) (ref : Ref H D O) : Except StepError FdId := do
  let .other payload := ref.value | throw (.invalidProgram "non-event description used as eventfd")
  let some id := store.untag payload | throw (.invalidProgram "non-event payload used as eventfd")
  unless id == ref.id do throw (.invalidProgram "eventfd payload/ownership identity mismatch")
  return id
private def isEvent (store : Store U O) (ref : Ref H D O) : Bool :=
  match ref.value with | .other payload => (store.untag payload).isSome | _ => false
private def getEvent (store : Store U O) (ref : Ref H D O) : MachineHooks.M K U EventFd.Event := do
  let id ← lift (eventId store ref)
  let found :=  (store.get (← get).machine.user).filter (·.1 == id)
  unless found.size == 1 do throw (.invalidProgram "eventfd state absent or ambiguous")
  let some (_,event) := found[0]? | throw (.invalidProgram "eventfd state index missing")
  return event
private def putEvent (store : Store U O) (ref : Ref H D O) (event : EventFd.Event) : MachineHooks.M K U Unit := do
  let id ← lift (eventId store ref)
  let _ ← getEvent store ref
  modify fun state => {state with machine := {state.machine with user := store.put ((store.get state.machine.user).map fun (old,value) => (old,if old == id then event else value)) state.machine.user}}

/-- Install this last-drop action in the shared readiness machine; a plain
FileMachine.dropReference would skip source watched-field destruction. -/
def withDestructor (store : Store U O) (machine : ReadinessMachine.Hooks K U H D O)
    (ready : Readiness.Hooks (MachineHooks.State K U) (Ref H D O)) : ReadinessMachine.Hooks K U H D O :=
  {machine with onLastDrop := fun ref => do
    if !isEvent store ref then machine.onLastDrop ref
    else
      let id ← lift (eventId store ref)
      ReadinessMachine.destroyWatched machine ready ref
      modify fun state => {state with machine := {state.machine with user := store.put ((store.get state.machine.user).filter (·.1 != id)) state.machine.user}}}

def physical [DecidableEq K] (store : Store U O) (machine : ReadinessMachine.Hooks K U H D O)
    (ready : Readiness.Hooks (MachineHooks.State K U) (Ref H D O))
    (wakeBudget : Nat) (access : PlaceMachine.AccessConfig K U)
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra) (choice : C)
    (libcI32 : String → MachineHooks.M K U Int32)
    (u64Layout : MachineHooks.M K U LocalLayout) :
    EventFd.PhysicalHooks (MachineHooks.State K U) (Ref H D O) :=
  let scalar := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  {
    libcI32 := libcI32
    u64Layout := u64Layout
    runtime := ready.runtime
    unblockThread := fun thread => ready.unblock thread .Eventfd
    getEvent := getEvent store
    putEvent := putEvent store
    cloneFd := FileMachine.cloneReference machine.files
    dropFd := ReadinessMachine.dropFd machine
    insertNew := fun event => do
      let id : FdId := ⟨(machine.files.table (← get).machine.user).nextId⟩
      let payload := store.tag id
      unless store.untag payload == some id do throw (.invalidProgram "eventfd payload embedding is not injective")
      let ref ← ReadinessMachine.newFd machine (fun _ => true) (.other payload)
      unless ref.id == id do throw (.invalidProgram "eventfd reservation identity changed")
      let entries := store.get (← get).machine.user
      if entries.any (·.1 == id) then throw (.invalidProgram "eventfd object identity collision")
      modify fun state => {state with machine := {state.machine with user := store.put (entries.push (id,event)) state.machine.user}}
      let (table,number) ← lift ((machine.files.table (← get).machine.user).insert ref)
      modify fun state => {state with machine := {state.machine with user := machine.files.setTable table state.machine.user}}
      return number
    readU32 := fun operand => do lift ((← scalar operand).toUInt32.mapError ScalarOps.scalarError)
    readI32 := fun operand => do lift ((← scalar operand).toInt32.mapError ScalarOps.scalarError)
    unaligned := fun pointer layout => do
      unless layout.layout.isSized do throw (.invalidProgram "ptr_to_mplace requires sized layout")
      return ⟨⟨pointer,.none,none⟩,layout⟩
    readU64 := fun buffer => do
      let immediate ← PlaceMachine.readImmediate access ⟨.indirect buffer.mplace,buffer.layout⟩
      let value ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
      lift (value.toUInt64.mapError ScalarOps.scalarError)
    writeU64 := fun value buffer => do
      let value ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) buffer.layout.layout.size |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar value) ⟨.memory buffer.mplace,buffer.layout⟩
    updateReadiness := fun fd => Readiness.updateFd wakeBudget (ReadinessMachine.bind machine ready) fd {forceEdge := true} }

def bind [DecidableEq K] (store : Store U O) (machine : ReadinessMachine.Hooks K U H D O)
    (ready : Readiness.Hooks (MachineHooks.State K U) (Ref H D O))
    (wakeBudget : Nat) (access : PlaceMachine.AccessConfig K U)
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra) (choice : C)
    (base : EventFd.Hooks (MachineHooks.State K U) (Ref H D O)) :
    EventFd.Hooks (MachineHooks.State K U) (Ref H D O) :=
  {toPhysicalHooks := physical store machine ready wakeBudget access place choice base.libcI32 base.u64Layout
   deferred := base.deferred}

/-- Route dynamic FileDescription IO to the source eventfd implementation.
ErrorKind conversion is the actual io::Error::from(kind) host constructor. -/
def bindFiles (store : Store U O) (event : EventFd.Hooks (MachineHooks.State K U) (Ref H D O))
    (retryBudget : Nat) (errorFromKind : IoError.ErrorKind → MachineHooks.M K U (IoError.Error Host))
    (base : Files.Hooks (MachineHooks.State K U) H D O Host Meta) :
    Files.Hooks (MachineHooks.State K U) H D O Host Meta :=
  let convert := fun (finish : Files.Finish (MachineHooks.State K U) Host) =>
    let body := fun result => do
      match result with
      | .ok count => finish (.ok count)
      | .error kind => finish (.error (← errorFromKind kind))
    (⟨body,finish.capture⟩ : EventFd.Finish (MachineHooks.State K U))
  {base with
    otherRead := fun fd communicate pointer length finish =>
      if isEvent store fd then EventFd.read event retryBudget fd pointer length (convert finish)
      else base.otherRead fd communicate pointer length finish
    otherWrite := fun fd communicate pointer length finish =>
      if isEvent store fd then EventFd.write event retryBudget fd pointer length (convert finish)
      else base.otherWrite fd communicate pointer length finish
    otherShortOperations := fun payload => if (store.untag payload).isSome then false else base.otherShortOperations payload
    otherReadiness := fun payload => do
      let some id := store.untag payload | return ← base.otherReadiness payload
      let entries := (store.get (← get).machine.user).filter (·.1 == id)
      unless entries.size == 1 do throw (.invalidProgram "eventfd readiness state absent or ambiguous")
      let some (_,value) := entries[0]? | throw (.invalidProgram "eventfd readiness state missing")
      return some (EventFd.readiness value)
    otherHasReadinessWatched := fun payload => (store.untag payload).isSome || base.otherHasReadinessWatched payload
    otherIsTerminal := fun payload communicate => if (store.untag payload).isSome then pure false else base.otherIsTerminal payload communicate }

/-- Shared readiness callbacks query the same authoritative event counter. -/
def bindReadiness (store : Store U O)
    (base : Readiness.Hooks (MachineHooks.State K U) (Ref H D O)) :
    Readiness.Hooks (MachineHooks.State K U) (Ref H D O) :=
  {base with readiness := fun fd => do
    if isEvent store fd then return EventFd.readiness (← getEvent store fd)
    base.readiness fd}

/-- The actual source metadata result is synthetic S_IFREG, not host metadata. -/
def metadataKind (store : Store U O) (payload : O) : Option String :=
  if (store.untag payload).isSome then some "S_IFREG" else none
end Miri.Interpreter.EventFdMachine
