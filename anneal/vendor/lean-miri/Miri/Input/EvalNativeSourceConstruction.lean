import Miri.Input.CompilerNative
import Miri.Input.EvalNativeConstruction
import Miri.Input.EvalNativeMachine
import Miri.Interpreter.NativeExecutor

/-! Source-owned assembly of native calls. Compiler ABI metadata is queried
from the prepared image and the live runtime-array registry. The remaining
inputs are narrow host operations: real symbol/address lookup, stable backing,
process-global tracing state, and the source supervisor/libffi boundary.
The resulting call always runs NativeMachine's canonical argument, exposure,
Tree Borrows, trace, return-write, and validity pipeline. -/
namespace Miri.Input.EvalNativeSourceConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-! These are external native operations, not a replacement `String → Bool`
foreign shim. In particular, `execute` retains the source interchange and
supervisor protocol and delegates only real libffi/process operations. -/
set_option autoImplicit false in
structure RawHost (U C N Code : Type) where
  exposePhysical : AllocId → Bool → NativeMachine.M MiriMemoryKind U Unit
  process : EvalNativeConstruction.Process U C
  lookupSymbol : C → N → String → NativeMachine.M MiriMemoryKind U
    (Option (Native.SymbolInfo Code))
  supervisor : Native.Trace.ChildHooks
    (NativeMachine.State MiriMemoryKind U) C
  ffi : (AllocId → Array UInt8 → NativeMachine.M MiriMemoryKind U Unit) →
    C → Code → Array Native.OwnedArg → Native.FfiType → Size →
    NativeMachine.M MiriMemoryKind U (Array UInt8)

/-! The array accessor must address the same `EvalWorld.World` carried by the
native-call state. It is supplied by the canonical Core configuration (for
source execution, `EvalProjectionMachine.arrays`). -/
set_option autoImplicit false in
def effects {U C N Code : Type}
    (hostBits : Nat)
    (lifecycleBacking : Option
      (NativeAllocationLifecycle.Backing (NativeMachine.State MiriMemoryKind U)))
    (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access (NativeMachine.State MiriMemoryKind U))
    (raw : RawHost U C N Code) :
    EvalNativeMachine.Effects U C N Code :=
  let compiler := CompilerNative.make p arrays
  let backing : EvalNativeConstruction.Backing U := match lifecycleBacking with
    | some lifecycle => EvalNativeConstruction.ownedBacking lifecycle raw.exposePhysical
    | none => {
        address := fun _ _ => throw (.unsupported "native allocation backing is unavailable")
        expose := raw.exposePhysical }
  let executor : NativeExecutor.Hooks MiriMemoryKind U C Code := {
    supervisor := raw.supervisor
    ffi := raw.ffi }
  EvalNativeConstruction.effects hostBits compiler backing raw.process
    raw.lookupSymbol executor

/-! Build the actual native call action over the caller's canonical memory and
validity providers. `NativeMachine.call` first searches the live loaded-library
vector, so an empty vector returns the source `false` result without demanding
symbol lookup, libffi, or tracing capabilities. -/
set_option autoImplicit false in
def call {Os R P H D O Aff B Poll Instant System N Profiler C Code F A Pad : Type}
    (hostBits : Nat)
    (lifecycleBacking : Option (NativeAllocationLifecycle.Backing
      (NativeMachine.State MiriMemoryKind
        (EvalNativeMachine.U Os R P H D O Aff B Poll Instant System N Profiler))))
    (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access (NativeMachine.State MiriMemoryKind
      (EvalNativeMachine.U Os R P H D O Aff B Poll Instant System N Profiler)))
    (raw : Option (RawHost
      (EvalNativeMachine.U Os R P H D O Aff B Poll Instant System N Profiler) C N Code))
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalNativeMachine.U Os R P H D O Aff B Poll Instant System N Profiler))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalNativeMachine.U Os R P H D O Aff B Poll Instant System N Profiler)))
    (validity : ValidityVisitor.Hooks Provenance
      (EvalNativeMachine.S Os R P H D O Aff B Poll Instant System N Profiler)
      C MachineHooks.FrameExtra F A Pad)
    (validationBudget reachabilityBudget : Nat) (choice : C) (fuel : Nat)
    (name : String) (destination : RuntimePlace Provenance)
    (arguments : Array (OpTy Provenance)) :
    NativeMachine.M MiriMemoryKind
      (EvalNativeMachine.U Os R P H D O Aff B Poll Instant System N Profiler) Bool :=
  do
    let state ← get
    if state.machine.user.payload.payload.user.host.nativeLibraries.isEmpty then
      return false
    let some raw := raw
      | throw (.unsupported "native source symbol/FFI backend is unavailable")
    EvalNativeMachine.call (effects hostBits lifecycleBacking p arrays raw) access pointers validity
      validationBudget reachabilityBudget choice fuel name destination
      (arguments.map FnArg.Copy)

end Miri.Input.EvalNativeSourceConstruction
