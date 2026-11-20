import Miri.Concurrency.TypedSyncRuntime
import Miri.Interpreter.SyncMachine

/-! Physical source synchronization arenas. References index source host objects;
callback tokens come exclusively from the shared ThreadMachine supply. The arena
contains no interpreter functions and has no independent token generator. -/
namespace Miri.Interpreter.TypedSyncMachine
open Miri.Concurrency Miri.Memory
abbrev User := ExecutionStateTransport.Inner
abbrev State K U := MachineHooks.State K (User U)
abbrev M K U A := MachineHooks.M K (User U) A
structure Views (U : Type) where
  storage : U → TypedSyncRuntime.Storage
  putStorage : U → TypedSyncRuntime.Storage → U
  nextCallback : U → Nat
  putNextCallback : U → Nat → U
private def payload : M K U U := return (← get).machine.user.payload.payload.user
private def modifyPayload (f : U → U) : M K U Unit :=
  modify fun s => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user := f s.machine.user.payload.payload.user}}}}}
private def storage (v : Views U) : M K U TypedSyncRuntime.Storage := return v.storage (← payload)
private def setStorage (v : Views U) (value : TypedSyncRuntime.Storage) : M K U Unit :=
  modifyPayload fun u => v.putStorage u value

def newObject (v : Views U) (object : TypedSyncRuntime.Object) : M K U TypedSyncRuntime.Ref := do
  let data ← storage v
  setStorage v {data with objects := data.objects.push object}
  pure ⟨data.objects.size⟩
def getObject (v : Views U) (ref : TypedSyncRuntime.Ref) : M K U TypedSyncRuntime.Object := do
  let some value := (← storage v).objects[ref.index]? | throw (.invalidProgram "missing source synchronization reference")
  pure value
def putObject (v : Views U) (ref : TypedSyncRuntime.Ref) (value : TypedSyncRuntime.Object) : M K U Unit := do
  let data ← storage v
  if bound : ref.index < data.objects.size then
    setStorage v {data with objects := data.objects.set ref.index value}
  else throw (.invalidProgram "missing source synchronization reference")
def owns (v : Views U) (token : Nat) : M K U Bool :=
  return (← storage v).callbacks.any (·.1 == token)
def register (v : Views U) (capture : TypedSyncRuntime.Capture) : M K U Nat := do
  let token := v.nextCallback (← payload)
  let data ← storage v
  if data.callbacks.any (·.1 == token) then throw (.invalidProgram "shared callback token collision")
  modifyPayload fun u => v.putNextCallback u (token+1)
  setStorage v {data with callbacks := data.callbacks.push (token,capture)}
  pure token
def take (v : Views U) (token : Nat) : M K U TypedSyncRuntime.Capture := do
  let data ← storage v
  let entries := data.callbacks.filter (·.1 == token)
  unless entries.size == 1 do throw (.callback "missing or ambiguous typed synchronization callback")
  let some (_,capture) := entries[0]? | throw (.invalidProgram "typed callback lookup invariant")
  setStorage v {data with callbacks := data.callbacks.filter (·.1 != token)}
  pure capture

/-- Source physical state and ownership are closed here. Remaining fields in
base are the concrete scalar/error writes and source configuration; they are
not an object store, callback evaluator, or synthetic clock. -/
def bind (v : Views U) (base : TypedSyncRuntime.Hooks (State K U)) :
    TypedSyncRuntime.Hooks (State K U) :=
  {base with
    global := return (← get).machine.dataRace
    putGlobal := fun global => modify fun s => {s with machine := {s.machine with dataRace := global}}
    threads := return (← get).machine.threads
    putThreads := fun manager => ExecutionStateTransport.reverseAction (ThreadStacks.installManager manager)
    get := getObject v
    put := putObject v
    register := register v
    take := take v
    cancel := fun token => do let _ ← take v token; pure ()
    error := SyncMachine.sourceError}
/-- Actual compiler/OS writes and immutable source configuration. No callback
or object-store fields are requested from the production caller. -/
structure Effects (S : Type) where
  handler : SyncClockHandler
  usizeBits : Nat
  communicate : Bool
  writeScalar : Int32 → TypedSyncRuntime.Dest → EStateM StepError S Unit
  writeInt : Int → TypedSyncRuntime.Dest → EStateM StepError S Unit
  errnoNegOne : String → TypedSyncRuntime.Dest → EStateM StepError S Unit
  windowsTrue : EStateM StepError S Int32
  windowsFalse : EStateM StepError S Int32
  windowsTimeoutError : EStateM StepError S Unit

def typed (v : Views U) (e : Effects (State K U)) : TypedSyncRuntime.Hooks (State K U) where
  handler := e.handler
  usizeBits := e.usizeBits
  communicate := e.communicate
  global := return (← get).machine.dataRace
  putGlobal := fun global => modify fun s => {s with machine := {s.machine with dataRace := global}}
  threads := return (← get).machine.threads
  putThreads := fun manager => ExecutionStateTransport.reverseAction (ThreadStacks.installManager manager)
  get := getObject v
  put := putObject v
  register := register v
  take := take v
  cancel := fun token => do let _ ← take v token; pure ()
  writeScalar := e.writeScalar
  writeInt := e.writeInt
  errnoNegOne := e.errnoNegOne
  windowsTrue := e.windowsTrue
  windowsFalse := e.windowsFalse
  windowsTimeoutError := e.windowsTimeoutError
  error := SyncMachine.sourceError

private def wrong : M K U A := throw (.invalidProgram "synchronization object has wrong source kind")
/-- Production SyncRuntime dictionary: its backend variant contains no Registry
S, dummy getter, or no-op setter. All source callbacks use the typed interpreter. -/
def runtime (v : Views U) (e : Effects (State K U)) :
    SyncRuntime.Hooks (State K U) TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest :=
  let h := typed v e
  { handler := e.handler, usizeBits := e.usizeBits, communicate := e.communicate
    global := h.global, putGlobal := h.putGlobal, threads := h.threads, putThreads := h.putThreads
    callbackBackend := .typed (register v) (TypedSyncRuntime.invoke h)
      (fun token => do let _ ← take v token; pure ()) (owns v)
    mutex := fun ref => do
      let .mutex value ← getObject v ref | wrong
      pure value
    putMutex := fun ref value => putObject v ref (.mutex value)
    rwlock := fun ref => do
      let .rwlock value ← getObject v ref | wrong
      pure value
    putRwlock := fun ref value => putObject v ref (.rwlock value)
    condvar := fun ref => do
      let .condvar value ← getObject v ref | wrong
      pure value
    putCondvar := fun ref value => putObject v ref (.condvar value)
    semaphore := fun ref => do
      let .semaphore value ← getObject v ref | wrong
      pure value
    putSemaphore := fun ref value => putObject v ref (.semaphore value)
    futex := fun ref => do
      let .futex value ← getObject v ref | wrong
      pure value
    putFutex := fun ref value => putObject v ref (.futex value)
    writeScalar := e.writeScalar
    error := SyncMachine.sourceError }

def initOnce (v : Views U) (e : Effects (State K U)) :
    InitOnce.Hooks (State K U) TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest where
  runtime := runtime v e
  get := fun ref => do
      let .initOnce value ← getObject v ref | wrong
      pure value
  put := fun ref value => putObject v ref (.initOnce value)
  new := newObject v (.initOnce {})
end Miri.Interpreter.TypedSyncMachine
