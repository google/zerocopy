import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalStartupMemoryConstruction
import Miri.Input.EvalTypedSyncMachine
import Miri.Input.EvalSyncObjectAccess

/-! Canonical source synchronization metadata access for the actual EvalWorld.
Every pinned Miri SyncObj family is represented by either its typed source
object in HostRuntime.sync or the Linux futex marker (whose source on_access
implementation is the trait default). There is no caller-provided access
callback and no successful fallback for an unrecognized metadata payload. -/
namespace Miri.Input.EvalSyncObjectConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Payload := EvalSyncObjectAccess.Payload

abbrev World Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalWorld.World Os R Payload H D O Aff B
    (HostRuntime.Storage Poll Instant System H D O Native Profiler)
abbrev User Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalCoreMachine.User Os R Payload H D O Aff B
    (HostRuntime.Storage Poll Instant System H D O Native Profiler)
abbrev Machine Os R H D O Aff B Poll Instant System Native Profiler :=
  PlaceMachine.Machine MiriMemoryKind
    (User Os R H D O Aff B Poll Instant System Native Profiler)
abbrev M Os R H D O Aff B Poll Instant System Native Profiler A :=
  PlaceMachine.MachineM MiriMemoryKind
    (User Os R H D O Aff B Poll Instant System Native Profiler) A

def typedEmbedding : TypedSyncObjectMachine.Payload Payload :=
  EvalSyncObjectAccess.typedEmbedding

def linuxFutexEmbedding : LinuxFutexMachine.Payload Payload :=
  EvalSyncObjectAccess.linuxFutexEmbedding

def onAccess : Payload → SyncObject.AccessKind →
    M Os R H D O Aff B Poll Instant System Native Profiler Unit :=
  EvalSyncObjectAccess.onAccess

/-- Compose the same canonical dispatcher with Miri's Linux futex-specific
default implementation. This is used when building LinuxFutexMachine hooks;
other source synchronization objects continue through `onAccess`. -/
def linuxFutexOnAccess : Payload → SyncObject.AccessKind →
    M Os R H D O Aff B Poll Instant System Native Profiler Unit :=
  EvalSyncObjectAccess.linuxFutexOnAccess

/-- Install the source-owned SyncObj access behavior into the rest of a real
EvalConfigurationCore input. The incoming `sync` field is intentionally
overwritten; it cannot choose memory semantics. -/
def withCanonicalAccess
    (leaves : EvalConfigurationCore.Leaves Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost) :
    EvalConfigurationCore.Leaves Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost :=
  {leaves with sync := onAccess}

/-- Source-specialized leaf binder. Its compiler/host state is the canonical
Unix SourceHost, and its synchronization payload is fixed to Miri's typed
objects plus Linux futex metadata. The source constructor cannot retain a
caller-selected synchronization policy. -/
def withCanonicalSourceAccess
    (leaves : EvalConfigurationCore.SourceLeaves
      Os R Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter) :
    EvalConfigurationCore.SourceLeaves
      Os R Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter :=
  {leaves with sync := onAccess}

/-- Final source Core closure with its synchronization access callback
constructed here. This is the production source-entry adapter: arbitrary
`SourceLeaves.sync` values are discarded before Core builds its fixed MIR
configuration. -/
def makeFromSource [DecidableEq Os]
    (prepared : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves
      Os R Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter)
    (choice : C) :=
  EvalConfigurationCore.makeFromSource prepared image bytes options
    (withCanonicalSourceAccess sourceLeaves) choice

/-- Source configuration constructor: all other compiler, memory, backend,
and host inputs are unchanged, while the per-object access callback is derived
from the actual world and source metadata sum. -/
def configuration
    (prepared : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : EvalConfigurationCore.Leaves Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost)
    (choice : C) : Nat → Except StepError
      (ExecutionMachine.Config MiriMemoryKind
        (User Os R H D O Aff B Poll Instant System Native Profiler)
        C O ABI.ExternAbi ClockHost) :=
  EvalConfigurationCore.make prepared image bytes options (withCanonicalAccess leaves) choice

def step
    (prepared : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : EvalConfigurationCore.Leaves Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost)
    (choice : C)
    (state : MachineHooks.State MiriMemoryKind
      (ExecutionStateTransport.Outer
        (World Os R H D O Aff B Poll Instant System Native Profiler))) :
    StepResult (MachineHooks.State MiriMemoryKind
      (ExecutionStateTransport.Outer
        (World Os R H D O Aff B Poll Instant System Native Profiler))) Bool :=
  EvalConfigurationCore.step prepared image bytes options (withCanonicalAccess leaves) choice state

def validateInitialization
    (leaves : EvalConfigurationCore.Leaves Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost) :
    EvalConfigurationCore.M Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) Unit :=
  EvalConfigurationCore.validateInitialization (withCanonicalAccess leaves)

/-- Startup argument/environment operations reuse the same metadata callback
as MIR stepping, allocation, and deallocation. -/
def environmentMemory [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost)
    (leaves : EvalConfigurationCore.Leaves Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C ClockHost)
    (spans : AllocationDriver.SpanHooks) (choice : C)
    (alignment : ValidityMachine.AlignmentCheck) (stringScanBudget : Nat) :
    EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupMemoryConstruction.InnerControl Os R Payload H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler)) C Payload :=
  EvalStartupMemoryConstruction.environmentMemory prepared execution
    (withCanonicalAccess leaves) spans choice alignment stringScanBudget

def sourceEnvironmentMemory [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R Payload H D
      (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
      (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
      C ClockHost)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves
      Os R Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter)
    (spans : AllocationDriver.SpanHooks) (choice : C)
    (alignment : ValidityMachine.AlignmentCheck) (stringScanBudget : Nat) :
    EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupMemoryConstruction.InnerControl Os R Payload H D
        (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
        (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C Payload := Id.run do
  let leaves := withCanonicalSourceAccess sourceLeaves
  let pointerSource : EvalPointerSource.Leaves Os R Payload H D
      (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
      (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := leaves.nativeHost
     }
  let extras : MemoryExtras.Hooks MiriMemoryKind
      (EvalAllocationMachine.User Os R Payload H D
        (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
        (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      Payload := EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer
  let source : EvalPointerSource.Constructed Os R Payload H D
      (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
      (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler) :=
    EvalPointerSource.make prepared.compiler prepared.image extras pointerSource
      choice
  let diagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (EvalAllocationMachine.User Os R Payload H D
        (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
        (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler)) Unit :=
    fun _ => pure ()
  let nativeDrop := pointerSource.nativeHost.map fun host =>
    NativeAllocationLifecycle.releaseAllocation
      (NativeAllocationLifecycle.liftBacking host.backing)
  let deallocate := fun pointer old kind =>
    EvalAllocationMachine.deallocateWith spans source.pointers extras
      diagnostic nativeDrop pointer old kind
  let arrays : RuntimeArrayQueries.Access
      (EvalHostRuntimeConstruction.RuntimeState
        (EvalStartupMemoryConstruction.InnerControl Os R Payload H D
          (EvalConfigurationCore.SourceOther Raw Listener TcpStream Error) Aff B
          (EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler))) := {
    get := fun state => EvalPointerSource.arrays.get state.machine
    set := fun state world => {state with machine := EvalPointerSource.arrays.set state.machine world} }
  return {
    access := execution.access
    allocation := execution.allocation
    deallocate
    pointers := source.pointers
    projection := execution.projection
    arrays
    symbolicAlignment := alignment == .Symbolic
    enforceAlignment := alignment != .None
    stringScanBudget
    choice
    pointerTy := prepared.layouts.arguments.u8Pointer.ty
    pointerLayout := prepared.layouts.unitPtrMut }

end Miri.Input.EvalSyncObjectConstruction
