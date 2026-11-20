import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalWindowsCallDispatchConstruction
import Miri.Input.EvalRuntimeConstruction

/-! Source-owned Windows configuration construction. Reuse the fixed MIR
engine while deriving its foreign factory from compiler facts, the actual
world and raw host leaves. No completed foreign dictionary is an input.
The context retains the same live assembly factory for startup and later
connection to Main/callbacks. -/
namespace Miri.Input.EvalWindowsConfigurationCore
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other := EvalWindowsCallDispatchConstruction.Other
abbrev Host := EvalWindowsCallDispatchConstruction.Host
abbrev State := EvalWindowsCallDispatchConstruction.State
abbrev CoreState := EvalWindowsCallDispatchConstruction.CoreState
abbrev Assembly := EvalWindowsCallDispatchConstruction.Assembly

abbrev Context Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
    Meta Path Zone Timestamp :=
  EvalConfigurationCore.ForeignContext Os R EvalSyncPayload.Payload H D
    (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant
    (Assembly Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Zone Timestamp)

/- Internal assembly edge used by the Windows startup implementation. The
public raw-leaf constructor below does not accept a guest hook replacement. -/
set_option autoImplicit false in
def makeWithSourceConnection
    {Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
      ErrorHost Meta Path AddrIter Zone Timestamp : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncPayload.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (windowsHost : EvalWindowsEnvironmentConstruction.HostEffects
      (State Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
        Raw Listener TcpStream Error) Os Error)
    (choice : C) (capacity : Nat)
    (connection : Option
      (Context Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
          Meta Path Zone Timestamp →
        Assembly Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
          Raw Listener TcpStream Error C Meta Path Zone Timestamp →
        EStateM StepError
          (CoreState Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error)
          (Assembly Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error C Meta Path Zone Timestamp)))
    (portableConnection : Option
      (Context Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
          Meta Path Zone Timestamp →
        ForeignItems.Hooks Provenance
          (CoreState Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error)
          (RuntimePlace Provenance) (RuntimePlace Provenance)
          (Pointer (Option Provenance)) LoadedBody CallInstance →
        EStateM StepError
          (CoreState Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error)
          (ForeignItems.Hooks Provenance
            (CoreState Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
              Raw Listener TcpStream Error)
            (RuntimePlace Provenance) (RuntimePlace Provenance)
            (Pointer (Option Provenance)) LoadedBody CallInstance)) := none) :
    Except StepError
      (ExecutionMachine.Config MiriMemoryKind
        (EvalConfigurationCore.SourceUser Os R EvalSyncPayload.Payload H D CpuAffinity.Mask B
          Poll Instant System Native Profiler Raw Listener TcpStream Error)
        C (Other Raw Listener TcpStream Error) ABI.ExternAbi Instant ×
       EvalConfigurationCore.ForeignContext Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant
        (Assembly Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
          Raw Listener TcpStream Error C Meta Path Zone Timestamp)) := do
  let liftedTarget ← match p.externStatics.targetFacts with
    | .ok facts => pure (⟨facts⟩ : ULift.{1} CompilerExternStatic.TargetFacts)
    | .error reason => throw (.unsupported reason)
  let target := liftedTarget.down
  unless target.os == "windows" do
    throw (.invalidProgram s!"Windows source configuration requested for `{target.os}`")
  unless windowsHost.communicate == sourceLeaves.hostConfiguration.communicate do
    throw (.invalidProgram "Windows host and source communication policies differ")
  unless windowsHost.communicate == (match windowsHost.isolatedOp with
      | .allow => true | .reject _ => false) do
    throw (.invalidProgram "Windows communication flag disagrees with isolation policy")
  let sourcePointer : EvalPointerSource.Leaves Os R EvalSyncPayload.Payload H D
      (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := sourceLeaves.nativeHost
     }
  let leaves : EvalConfigurationCore.Leaves Os R EvalSyncPayload.Payload H D
      (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant := {
    pointerSource := sourcePointer
    sync := EvalSyncObjectAccess.onAccess
    storage := sourceLeaves.storage
    spans := sourceLeaves.spans
    foreign := none
    dynSymName := sourceLeaves.dynSymName
    checkLlvmSymbolClash := sourceLeaves.checkLlvmSymbolClash
    math := sourceLeaves.math
    mathError := sourceLeaves.mathError
    control := sourceLeaves.control
    blockingSources := sourceLeaves.blockingSources }
  let builder : EvalConfigurationCore.ForeignBuilder Os R EvalSyncPayload.Payload H D
      (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant
      (Assembly Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
        Raw Listener TcpStream Error C Meta Path Zone Timestamp) := fun context => do
    let rawMemory ← match EvalConfigurationCore.environmentMemoryFromCore p context.access
        context.allocation context.extras context.deallocationDiagnostic context.nativeDrop
        context.pointers context.spans context.projection context.choice
        sourceLeaves.foreignSource.alignment sourceLeaves.foreignSource.stringScanBudget with
      | .ok memory => pure memory
      | .error error => throw error
    -- Only EnvironmentMemory's unused payload parameter changes here. Every
    -- effect and lens is retained from this exact Core context.
    let memory : EvalWindowsEnvironmentConstruction.Memory Os R EvalSyncPayload.Payload H D
        (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C := {
      access := rawMemory.access
      allocation := rawMemory.allocation
      deallocate := rawMemory.deallocate
      pointers := rawMemory.pointers
      projection := rawMemory.projection
      arrays := rawMemory.arrays
      symbolicAlignment := rawMemory.symbolicAlignment
      enforceAlignment := rawMemory.enforceAlignment
      stringScanBudget := rawMemory.stringScanBudget
      choice := rawMemory.choice
      pointerTy := rawMemory.pointerTy
      pointerLayout := rawMemory.pointerLayout }
    let ioHost : EvalUnixConstruction.IoHostEffects
        (State Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
          Raw Listener TcpStream Error) Error := {
      hostErrno := fun name => ExecutionStateTransport.action
        (sourceLeaves.foreignSource.host.ioError.hostErrno name)
      hostFromRaw := fun value => ExecutionStateTransport.action
        (sourceLeaves.foreignSource.host.ioError.hostFromRaw value)
      hostFromKind := fun kind => ExecutionStateTransport.action
        (sourceLeaves.foreignSource.host.ioError.hostFromKind kind) }
    let nativeLifecycleBacking := sourceLeaves.nativeHost.map fun host =>
      NativeAllocationLifecycle.liftBacking host.backing
    let assembled ← EvalWindowsCallDispatchConstruction.fromSource p
      (fun state => state.machine.user.payload.payload.user.host.nativeLibraries.map Prod.fst)
      (fun name destination args =>
        EvalNativeSourceConstruction.call
          sourceLeaves.hostConfiguration.hostUsizeBits nativeLifecycleBacking p
          EvalProjectionMachine.arrays sourceLeaves.nativeBackend context.validityAccess
          context.pointers context.validity options.limits.validation
          options.limits.callDispatch context.choice options.compatibilityBudget name
          (RuntimePlace.mk (.memory destination.mplace) destination.layout) args)
      context.validityAccess context.allocation
      context.extras context.deallocationDiagnostic context.nativeDrop context.pointers
      context.spans context.place (EvalRuntimeConstruction.outerPlaceHooks context.place)
      context.callFunction context.choice sourceLeaves.foreignSource.host.os
      sourceLeaves.foreignSource.host.environment memory windowsHost ioHost
      options.compatibilityBudget options.place.debugAssertions options.userRelevantCrates
    let assembled ← match connection with
      | none => pure assembled
      | some connect => connect context assembled
    let hostFill := sourceLeaves.foreignSource.host.getrandom.map fun operation count =>
      ExecutionStateTransport.action (operation count)
    let foreign ← match EvalWindowsCallDispatchConstruction.foreignFromAssembly p assembled
        context.math sourceLeaves.hostConfiguration hostFill with
      | .ok hooks => pure hooks
      | .error error => throw error
    let foreign := EvalForeignConstruction.bindMemory p context.validityAccess context.pointers
      context.place memory.symbolicAlignment memory.enforceAlignment context.choice
      sourceLeaves.foreignSource.stringScanBudget foreign
    let foreign := EvalPortableForeignRuntime.bindBacktrace p image context.functions
      context.access context.pointers.arithmetic context.projection context.choice
      (2 ^ sourceLeaves.hostConfiguration.hostUsizeBits - 1) foreign
    let foreign ← match portableConnection with
      | none => pure foreign
      | some connect => connect context foreign
    pure (foreign,assembled)
  EvalConfigurationCore.makeWithForeignContext p image bytes options leaves choice
    (some sourceLeaves.hostConfiguration) (some builder) capacity

set_option autoImplicit false in
def makeFromSourcePackage
    {Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
      ErrorHost Meta Path AddrIter Zone Timestamp : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncPayload.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (windowsHost : EvalWindowsEnvironmentConstruction.HostEffects
      (State Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
        Raw Listener TcpStream Error) Os Error)
    (choice : C) (capacity : Nat) :
    Except StepError
      (ExecutionMachine.Config MiriMemoryKind
        (EvalConfigurationCore.SourceUser Os R EvalSyncPayload.Payload H D CpuAffinity.Mask B
          Poll Instant System Native Profiler Raw Listener TcpStream Error)
        C (Other Raw Listener TcpStream Error) ABI.ExternAbi Instant ×
       Context Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
         Meta Path Zone Timestamp) :=
  makeWithSourceConnection p image bytes options sourceLeaves windowsHost choice capacity none

end Miri.Input.EvalWindowsConfigurationCore
