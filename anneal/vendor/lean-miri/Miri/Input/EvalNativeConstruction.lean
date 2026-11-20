import Miri.Input.EvalNativeMachine
import Miri.Interpreter.NativeExecutor
import Miri.Interpreter.NativeAllocationLifecycle

/-! Direct native production-effect construction. The source supervisor and
interchange policy are actual NativeExecutor operations; only compiler queries,
real library/backing operations and process-global observations are inputs. -/
namespace Miri.Input.EvalNativeConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
structure Compiler (U C : Type) where
  typeShape : C → LocalLayout → NativeMachine.M MiriMemoryKind U Native.TypeShape
  layoutOf : C → TyId → NativeMachine.M MiriMemoryKind U (Except Unit LocalLayout)
structure Backing (U : Type) where
  address : AllocId → NativeMachine.Data → NativeMachine.M MiriMemoryKind U Nat
  expose : AllocId → Bool → NativeMachine.M MiriMemoryKind U Unit
/-- Persistent source allocator access is supplied by the canonical backing
owner. It must refer to the same store used by Allocation creation/drop; this
record does not create a second AllocId/address registry. -/
structure IsolatedBacking (U : Type) where
  storage : NativeIsolatedAlloc.Access (NativeMachine.State MiriMemoryKind U)
  host : NativeAllocBytes.Host (NativeMachine.State MiriMemoryKind U)

def initializeIsolated (backing : IsolatedBacking U) : NativeMachine.M MiriMemoryKind U Unit := do
  let storage ← NativeIsolatedAlloc.create backing.host.allocator
  modify fun state => backing.storage.put state storage

def isolatedFromBytes (backing : IsolatedBacking U) (bytes : Array UInt8) (align : Nat) :
    NativeMachine.M MiriMemoryKind U NativeAllocBytes.Buffer :=
  NativeAllocBytes.fromBytes backing.storage backing.host bytes align

def isolatedZeroed (backing : IsolatedBacking U) (size align : Nat) :
    NativeMachine.M MiriMemoryKind U NativeAllocBytes.Buffer :=
  NativeAllocBytes.zeroed backing.storage backing.host size align

def isolatedDrop (backing : IsolatedBacking U) (buffer : NativeAllocBytes.Buffer) :
    NativeMachine.M MiriMemoryKind U Unit :=
  NativeAllocBytes.release backing.storage backing.host buffer

/-- The lifecycle selects the actual source allocator before ID reservation. -/
def isolatedLifecycleBacking (backing : IsolatedBacking U) :
    NativeAllocationLifecycle.Backing (NativeMachine.State MiriMemoryKind U) where
  isolated := true
  zeroed := fun size align => do
    return some (← NativeAllocBytes.zeroed backing.storage backing.host size.bytes.toNat (← NativeAllocationLifecycle.alignmentBytes align))
  fromBytes := fun bytes align => do NativeAllocBytes.fromBytes backing.storage backing.host bytes (← NativeAllocationLifecycle.alignmentBytes align)
  copyInto := fun buffer bytes => backing.host.copyFrom buffer.pointer bytes
  snapshot := NativeAllocBytes.snapshot backing.host
  release := NativeAllocBytes.release backing.storage backing.host

def globalLifecycleBacking (host : NativeAllocBytes.GlobalHost (NativeMachine.State MiriMemoryKind U)) :
    NativeAllocationLifecycle.Backing (NativeMachine.State MiriMemoryKind U) where
  isolated := false
  zeroed := fun size align => do NativeAllocBytes.globalAllocate host ⟨size.bytes.toNat,(← NativeAllocationLifecycle.alignmentBytes align)⟩ true
  fromBytes := fun bytes align => do NativeAllocBytes.globalFromBytes host bytes (← NativeAllocationLifecycle.alignmentBytes align)
  copyInto := fun buffer bytes => host.copyFrom buffer.pointer bytes
  snapshot := NativeAllocBytes.globalSnapshot host
  release := NativeAllocBytes.globalRelease host

/-- Canonical native address consumes Allocation-owned backing. Interpreter
byte writes are flushed into that same storage before native exposure; no
allocation or second address registry is created during FFI preparation. -/
def ownedBacking (backing : NativeAllocationLifecycle.Backing (NativeMachine.State MiriMemoryKind U))
    (expose : AllocId → Bool → NativeMachine.M MiriMemoryKind U Unit) : Backing U where
  address := fun _ allocation => do
    let some owner := allocation.nativeBuffer | throw (.invalidProgram "native allocation lacks lifecycle-owned backing")
    let bytes ← match allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len with
      | .ok bytes => pure bytes
      | .error error => throw (.invalidProgram s!"native canonical byte inspection: {reprStr error}")
    NativeAllocationLifecycle.commitBytes backing owner bytes allocation.align
    match NativeAllocationLifecycle.address allocation with
    | .ok address => pure address
    | .error reason => throw (.invalidProgram reason)
  expose := expose

structure Process (U C : Type) where
  tracingEnabled : NativeMachine.State MiriMemoryKind U → Bool
  warningEmitted : NativeMachine.State MiriMemoryKind U → Bool
  setWarningEmitted : NativeMachine.State MiriMemoryKind U → Bool → NativeMachine.State MiriMemoryKind U
  diagnosticSharedMemory : C → Bool → NativeMachine.M MiriMemoryKind U Unit

/-- hostBits is the actual configured host usize width. Lookup operates on the
actual World-loaded handle selected by EvalNativeMachine, retaining the source
vector index even when library path strings repeat. -/
def effects (hostBits : Nat) (compiler : Compiler U C) (backing : Backing U)
    (process : Process U C)
    (lookupSymbol : C → N → String → NativeMachine.M MiriMemoryKind U (Option (Native.SymbolInfo Code)))
    (executor : NativeExecutor.Hooks MiriMemoryKind U C Code) :
    EvalNativeMachine.Effects U C N Code where
  hostBits := hostBits
  typeShape := compiler.typeShape
  layoutOf := compiler.layoutOf
  lookupSymbol := lookupSymbol
  tracingEnabled := process.tracingEnabled
  backingAddress := backing.address
  exposePhysical := backing.expose
  warningEmitted := process.warningEmitted
  setWarningEmitted := process.setWarningEmitted
  diagnosticSharedMemory := process.diagnosticSharedMemory
  execute := NativeExecutor.execute executor
end Miri.Input.EvalNativeConstruction
