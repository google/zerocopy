import Miri.Input.EvalPointerSource
import Miri.Input.CompilerThreadLocal

/-! concurrency/thread.rs:629–667 on the actual EvalWorld. The existing
ThreadManager map is authoritative and runtime.tls.statics retains its typed
strict pointers for GC and thread-exit cleanup. Byte relocation, fresh identity,
TLS-kind insertion, root addressing and publication operate on one machine;
the legacy dual-memory insertAllocation adapter is not used. -/
namespace Miri.Input.EvalThreadLocalSource
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
open Miri.Memory.AllocAddresses
abbrev User := EvalCoreMachine.User
abbrev Machine := EvalPointerSource.Machine
abbrev M := EvalPointerSource.M

private def data (user : User Os R P H D O Aff B Host) : ThreadTlsMachine.Data :=
  user.payload.payload.user.runtime.tls

private def putData (user : User Os R P H D O Aff B Host) (value : ThreadTlsMachine.Data) : User Os R P H D O Aff B Host :=
  {user with payload := {user.payload with payload := {user.payload.payload with user :=
    {user.payload.payload.user with runtime := {user.payload.payload.user.runtime with tls := value}}}}}

private def compiler (value : Except String A) : M Os R P H D O Aff B Host A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported s!"TLS compiler query: {reason}")

private def cached (definition : MIR.DefId) : M Os R P H D O Aff B Host (Option (Pointer Provenance)) := do
  let machine ← get
  let entries := machine.threads.threadLocalAllocs.filter fun entry =>
    entry.definitionToken == definition && entry.thread == machine.threads.activeThread
  if entries.isEmpty then return none
  unless entries.length == 1 do throw (.invalidProgram "TLS allocation map has duplicate active-thread entries")
  let some entry := entries.head? | throw (.invalidProgram "TLS allocation map entry vanished")
  let pointers := (data machine.user).statics.filter fun pointer => pointer.runtimeId.value.toNat == entry.pointerToken
  unless pointers.size == 1 do throw (.invalidProgram "TLS allocation token lacks unique typed pointer")
  let some pointer := pointers[0]? | throw (.invalidProgram "TLS typed pointer vanished")
  unless pointer.definition == definition && pointer.thread == machine.threads.activeThread do
    throw (.invalidProgram "TLS typed pointer disagrees with canonical thread map")
  let .concrete id _ := pointer.pointer.provenance
    | throw (.invalidProgram "TLS strict pointer has wildcard provenance")
  unless id == pointer.runtimeId do throw (.invalidProgram "TLS strict pointer allocation identity mismatch")
  return some pointer.pointer

private def byteView (allocation : Allocation P E) : M Os R Payload H D O Aff B Host (Array UInt8) :=
  match allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len with
  | .ok bytes => pure bytes
  | .error error => throw (.invalidProgram s!"TLS initializer byte inspection: {reprStr error}")

/-- Fresh TLS bytes use from_bytes, unlike compiler globals' prepared-owner
take. The source allocation ID does not exist until after relocation succeeds. -/
private def copy (p : CompilerProviders.Prepared)
    (leaves : EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (source : EvalPointerSource.Constructed Os R P H D O Aff B Host)
    (allocation : Allocation CtfeProvenance Unit) :
    M Os R P H D O Aff B Host (Allocation Provenance Unit) := do
  let bytes ← byteView allocation
  let native := !(leaves.nativeLibraryPaths (← get).user.payload.payload.user.host).isEmpty
  let (bytes,owner) ← if native then do
      let some host := leaves.nativeHost | throw (.unsupported "native TLS copy requires actual byte backing")
      NativeAllocationLifecycle.prepareBytes host.backing bytes allocation.align
    else pure (bytes,none)
  try
    let converted ← fun machine =>
      match Allocation.adjustFromTcx allocation p.runtime.target.base
          (fun _ _ state => .ok bytes state) source.rootPointer machine with
      | .ok value machine => .ok value machine
      | .error (.pointerAdjustment error) machine | .error (.byteConversion error) machine => .error error machine
      | .error (.allocation error) machine => .error (.invalidProgram s!"TLS allocation conversion: {reprStr error}") machine
    let converted ← match owner with
      | none => pure converted
      | some owner =>
        let some host := leaves.nativeHost | throw (.unsupported "native TLS byte commit requires actual backing")
        NativeAllocationLifecycle.commitBytes host.backing owner (← byteView converted) converted.align
        match converted.attachNativeBuffer owner with
        | .ok value => pure value
        | .error reason => throw (.invalidProgram s!"TLS byte ownership: {reason}")
    pure (converted.withMutability .Mut)
  catch error =>
    if let some owner := owner then
      let some host := leaves.nativeHost | throw (.unsupported "native TLS copy cleanup requires actual backing")
      NativeAllocationLifecycle.releaseBytes host.backing owner allocation.byteSize allocation.align
    throw error

private def publish (definition : MIR.DefId) (id : AllocId) (pointer : Pointer Provenance) :
    M Os R P H D O Aff B Host Unit := do
  let machine ← get
  let thread := machine.threads.activeThread
  if machine.threads.threadLocalAllocs.any (fun entry => entry.definitionToken == definition && entry.thread == thread) then
    throw (.invalidProgram "TLS static initialized twice for one thread")
  let tls := data machine.user
  if tls.statics.any (fun entry => entry.definition == definition && entry.thread == thread) then
    throw (.invalidProgram "TLS typed registry contains an unpublished duplicate")
  let threads := {machine.threads with threadLocalAllocs :=
    machine.threads.threadLocalAllocs ++ [⟨definition,thread,id.value.toNat⟩]}
  let tls := {tls with statics := tls.statics.push ⟨definition,thread,id,pointer⟩}
  set {machine with threads, user := putData machine.user tls}

def getOrCreate (p : CompilerProviders.Prepared) (maximum : Size)
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (leaves : EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (source : EvalPointerSource.Constructed Os R P H D O Aff B Host)
    (definition : MIR.DefId) : M Os R P H D O Aff B Host (Pointer Provenance) := do
  if let some pointer ← cached definition then return pointer
  let entry ← compiler (CompilerThreadLocal.forDefinition p.program definition)
  if entry.info.foreignItem then throw (.unsupported "foreign thread-local statics are not supported")
  let some initializer := entry.initializer | throw (.unsupported "TLS initializer compiler evidence missing")
  let initializer ← compiler (AllocationImage.decode p.runtime.target (← get).memory initializer)
  let allocation ← copy p leaves source initializer
  try
    if allocation.byteSize.bytes > maximum.bytes then throw (.resourceExhaustion "TLS allocation exceeds maximum object size")
    let machine ← get
    let (memory,reserved) := machine.memory.reserveAllocId
    set {machine with memory}
    let id ← match reserved with
      | .ok id => pure id
      | .error error => throw (.resourceExhaustion s!"TLS allocation identity: {reprStr error}")
    -- TLS and Global share the source zero/main-thread allocation clocks and
    -- may-leak/no-allocation-span category; TrackingAlloc is display-only.
    let tree ← GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id allocation.byteSize allocation.align
    modify fun machine => {machine with memory := {machine.memory with
      live := machine.memory.live.push (id,⟨.machine .tls,allocation.withExtra tree⟩)}}
    let tag ← match (← get).borrowTracker with
      | none => pure BorTag.one
      | some tracker => match tracker.global.rootTag? id with
        | some tag => pure tag
        | none => throw (.invalidProgram "TLS allocation missing initialized root tag")
    let address ← MachineAddress.addrFromAllocId EvalPointerSource.tape source.address id (some .other)
    let pointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes address)
    publish definition id pointer
    pure pointer
  catch error =>
    if allocation.nativeBuffer.isSome then
      let retained := (← get).memory.live.any fun (_,entry) => entry.allocation.nativeBuffer == allocation.nativeBuffer
      unless retained do
        let some host := leaves.nativeHost | throw (.unsupported "native TLS insertion cleanup requires actual backing")
        NativeAllocationLifecycle.releaseAllocation host.backing allocation
    throw error

/-- Lift only the actual machine transition; the active MIR stack and shared
ThreadStacks registry survive unchanged, including failed initialization. -/
def hook (p : CompilerProviders.Prepared) (maximum : Size)
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (leaves : EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (source : EvalPointerSource.Constructed Os R P H D O Aff B Host)
    (_ : C) (definition : MIR.DefId) : MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) (Pointer (Option Provenance)) := do
  let pointer ← NativeAllocationLifecycle.liftMachineAction (getOrCreate p maximum extras leaves source definition)
  pure pointer.withOptionalProvenance

end Miri.Input.EvalThreadLocalSource
