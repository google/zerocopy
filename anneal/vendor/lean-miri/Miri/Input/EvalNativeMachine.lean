import Miri.Input.EvalWorld
import Miri.Input.HostRuntime
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.NativeMachine

/-! Actual native loaded-library binding on the canonical World.host vector.
Process-global tracing/FFI effects remain required external capabilities; no
second native handle table or source-safe result is manufactured. -/
namespace Miri.Input.EvalNativeMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev Host := HostRuntime.Storage
abbrev W Os R P H D O Aff B Poll Instant System N Profiler :=
  EvalWorld.World Os R P H D O Aff B (Host Poll Instant System H D O N Profiler)
abbrev U Os R P H D O Aff B Poll Instant System N Profiler :=
  ThreadStacks.Storage (W Os R P H D O Aff B Poll Instant System N Profiler)
abbrev S Os R P H D O Aff B Poll Instant System N Profiler :=
  ValidityMachine.State MiriMemoryKind (U Os R P H D O Aff B Poll Instant System N Profiler)

/-- Genuine compiler/native process/host effects. Symbol lookup receives the
actual loaded handle, and must perform source dlsym+dladdr/path conversion. -/
structure Effects (U C N Code : Type) where
  hostBits : Nat
  typeShape : C → LocalLayout → NativeMachine.M MiriMemoryKind U Native.TypeShape
  layoutOf : C → TyId → NativeMachine.M MiriMemoryKind U (Except Unit LocalLayout)
  lookupSymbol : C → N → String → NativeMachine.M MiriMemoryKind U (Option (Native.SymbolInfo Code))
  tracingEnabled : NativeMachine.State MiriMemoryKind U → Bool
  backingAddress : AllocId → NativeMachine.Data → NativeMachine.M MiriMemoryKind U Nat
  exposePhysical : AllocId → Bool → NativeMachine.M MiriMemoryKind U Unit
  warningEmitted : NativeMachine.State MiriMemoryKind U → Bool
  setWarningEmitted : NativeMachine.State MiriMemoryKind U → Bool → NativeMachine.State MiriMemoryKind U
  diagnosticSharedMemory : C → Bool → NativeMachine.M MiriMemoryKind U Unit
  execute : (AllocId → Array UInt8 → NativeMachine.M MiriMemoryKind U Unit) → C → Code → Array Native.OwnedArg →
    Native.FfiType → Size → NativeMachine.M MiriMemoryKind U (Array UInt8 × Option (Array Native.AccessEvent))

def host (effects : Effects (U Os R P H D O Aff B Poll Instant System N Profiler) C N Code) :
    NativeMachine.Host MiriMemoryKind (U Os R P H D O Aff B Poll Instant System N Profiler) C Code where
  hostBits := effects.hostBits
  typeShape := effects.typeShape
  layoutOf := effects.layoutOf
  libraries := fun state => state.machine.user.payload.payload.user.host.nativeLibraries.map fun (path,_) => ⟨path⟩
  lookupSymbol := fun choice index library name => do
    let libraries := (← get).machine.user.payload.payload.user.host.nativeLibraries
    let some (path,handle) := libraries[index]?
      | throw (.invalidProgram "native library source index unavailable")
    unless path == library.path do throw (.invalidProgram "native library source descriptor disagrees with loaded handle")
    effects.lookupSymbol choice handle name
  tracingEnabled := effects.tracingEnabled
  backingAddress := effects.backingAddress
  exposePhysical := effects.exposePhysical
  warningEmitted := effects.warningEmitted
  setWarningEmitted := effects.setWarningEmitted
  diagnosticSharedMemory := effects.diagnosticSharedMemory
  execute := effects.execute

/-- Native calls share the same physical access, address/exposure map, typed
validity visitor and loaded host handles as ordinary instruction execution. -/
def call (effects : Effects (U Os R P H D O Aff B Poll Instant System N Profiler) C N Code)
    (access : ValidityMachine.Access MiriMemoryKind (U Os R P H D O Aff B Poll Instant System N Profiler))
    (pointers : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (U Os R P H D O Aff B Poll Instant System N Profiler)))
    (validity : ValidityVisitor.Hooks Provenance (S Os R P H D O Aff B Poll Instant System N Profiler) C MachineHooks.FrameExtra F A Pad)
    (validationBudget reachabilityBudget : Nat) (choice : C) (fuel : Nat)
    (name : String) (dest : RuntimePlace Provenance) (args : Array (FnArg Provenance)) :
    NativeMachine.M MiriMemoryKind (U Os R P H D O Aff B Poll Instant System N Profiler) Bool :=
  NativeMachine.call (host effects) access pointers validity validationBudget reachabilityBudget
    choice fuel name dest (args.map FnArg.copyFnArg)
end Miri.Input.EvalNativeMachine
