import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.EvalCallRuntime
import Miri.Interpreter.MiriShimMachine
import Miri.Interpreter.MachineGCRoots

/-! Physical source construction for Miri-only portable foreign operations.
Memory, allocation identity, unwind, bookkeeping, and provenance collection
are derived from the same live EvalWorld as execution. Host and
diagnostic leaves remain in `EvalMiriHostEffectsConstruction`. -/
namespace Miri.Input.EvalMiriSourceConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalConfigurationCore.SourceOther Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev Stored Os R P H D O Aff B Host := EvalCoreMachine.Stored Os R P H D O Aff B Host
abbrev Control Os R P H D O Aff B Host :=
  ValidityMachine.Control (Stored Os R P H D O Aff B Host)
abbrev M Os R P H D O Aff B Host A :=
  MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A

private def query {Os R P H D O Aff B Host A : Type}
    (value : Except String A) :
    MachineHooks.M MiriMemoryKind
      (EvalCoreMachine.User Os R P H D O Aff B Host) A :=
  match value with
  | .ok result => pure result
  | .error reason => throw (.unsupported s!"Miri compiler primitive layout: {reason}")

/-- Project the exact persistent root-bearing World fields through the
canonical inner/outer state reassociation. GC sees the whole machine, while
address and symbolic-alignment updates remain in the single PointerMachine
record used by casts and allocation lookup. -/
private def gcHooks
    (Os R P H D O Aff B Host : Type) :
    ProvenanceGC.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) := by
  let visitUser := fun
      (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
      (roots : ProvenanceGC.Roots) =>
    MachineGCRoots.visit EvalWorld.roots (ExecutionStateTransport.outward state) roots
  let getOuter := fun (user : User Os R P H D O Aff B Host) =>
    ExecutionStateTransport.toOuter user
  exact {
    visitUser
    addresses := fun user => (EvalWorld.addresses.get (getOuter user)).addresses
    setAddresses := fun value user =>
      let outer := getOuter user
      let addressUser := EvalWorld.addresses.get outer
      let updated := EvalWorld.addresses.put outer {addressUser with addresses := value}
      ExecutionStateTransport.toInner updated
    symbolicAlignment := fun user => (EvalWorld.addresses.get (getOuter user)).symbolicAlignment
    setSymbolicAlignment := fun value user =>
      let outer := getOuter user
      let addressUser := EvalWorld.addresses.get outer
      let updated := EvalWorld.addresses.put outer
        {addressUser with symbolicAlignment := value}
      ExecutionStateTransport.toInner updated }

/-- Build physical Miri operations from the source-owned Core context. The
source static-root list is the exact TLS leak-check list; tracked allocations
use the persistent World set initialized from InitialMachine.Configuration.
No complete Miri hooks or caller-selected bookkeeping callbacks cross this
boundary. -/
def fromContext [DecidableEq MiriMemoryKind]
    {Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C ClockHost Assembly : Type}
    (options : EvalConfigurationCore.Options)
    (context : EvalConfigurationCore.ForeignContext Os R P H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
      C ClockHost Assembly) :
    MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C MachineHooks.FrameExtra (Other Raw Listener TcpStream Error) := Id.run do
  let user := fun
      (control : Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)) =>
    control.payload.user
  let bookkeeping : Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) →
      MiriShimMachine.Bookkeeping := fun control => {
    trackedAllocations := (user control).trackedAllocations
    staticRoots := (user control).runtime.tls.staticRoots }
  let setBookkeeping : MiriShimMachine.Bookkeeping →
      Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) →
      Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) :=
    fun (value : MiriShimMachine.Bookkeeping) control =>
    let stored := control.payload
    let world := stored.user
    let runtime := world.runtime
    let updatedRuntime := {runtime with tls := {runtime.tls with staticRoots := value.staticRoots}}
    {control with payload := {stored with user :=
      {world with trackedAllocations := value.trackedAllocations, runtime := updatedRuntime}}}
  let compiler := context.prepared
  let u64Layout := fun (_ : C) => do
    let raw ← query (compiler.primitiveLayout "u64")
    return (⟨raw.ty, raw.layout⟩ : LocalLayout)
  let boolLayout := fun (_ : C) => do
    let raw ← query (compiler.primitiveLayout "bool")
    return (⟨raw.ty, raw.layout⟩ : LocalLayout)
  let usizeLayout := fun (_ : C) => do
    let raw ← query (compiler.primitiveLayout "usize")
    return (⟨raw.ty, raw.layout⟩ : LocalLayout)
  let unwind := EvalCallRuntime.unwind context.access context.projection context.functions
    options.panicUnwinds context.callFunction
  return {
    access := context.access
    pointer := context.pointers
    place := context.place
    bookkeeping
    setBookkeeping
    cAllocation := fun kind => kind == .machine .c
    u64Layout
    boolLayout
    usizeLayout
    unwind
    gc := gcHooks Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) }

end Miri.Input.EvalMiriSourceConstruction
