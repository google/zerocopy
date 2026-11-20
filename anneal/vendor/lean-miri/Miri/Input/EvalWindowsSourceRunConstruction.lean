import Miri.Input.EvalBootstrap
import Miri.Input.EvalCallbackSyncConstruction
import Miri.Input.EvalPreparation
import Miri.Input.EvalSourceRunConstruction
import Miri.Input.EvalWindowsCallbackSourceConstruction
import Miri.Input.EvalWindowsCallbackAssembly
import Miri.Input.EvalWindowsConnectedSourceAssembly
import Miri.Input.EvalWindowsConfigurationCore
import Miri.Input.EvalWindowsRunConstruction
import Miri.Input.EvalWindowsSyncTimeConstruction
import Miri.Input.EvalMiriSourceConstruction
import Miri.Input.EvalMiriHostEffectsConstruction
import Miri.Input.EvalMiriSourceRuntime
import Miri.Input.EvalMiriTreeDiagnostics
import Miri.Input.CompilerFacts
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.ExecutionForeignTransport

/-! Canonical Windows source startup. The factory builds the fixed MIR
configuration and live Windows foreign context from raw source leaves. This
unit builds its initial assembly, bootstraps the same Main state, and derives
typed-sync and Windows callback routing for the Windows component connector
and loop. -/
namespace Miri.Input.EvalWindowsSourceRunConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Other Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.Other Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalWindowsCallDispatchConstruction.Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsCallDispatchConstruction.State Os R H D CpuAffinity.Mask B Poll Instant System
    Native Profiler Raw Listener TcpStream Error
abbrev Assembly Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp :=
  EvalWindowsCallDispatchConstruction.Assembly Os R H D CpuAffinity.Mask B Poll Instant System
    Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp
abbrev Context Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error C Meta Path Zone Timestamp :=
  EvalWindowsConfigurationCore.Context Os R H D B Poll Instant System Native Profiler C
    Raw Listener TcpStream Error Meta Path Zone Timestamp

set_option autoImplicit false in
structure Started
    (Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
      ErrorHost Meta Path : Type) where
  execution : ExecutionMachine.Config MiriMemoryKind
    (EvalConfigurationCore.SourceUser Os R EvalSyncObjectAccess.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    C (Other Raw Listener TcpStream Error) ABI.ExternAbi Instant
  context : Context Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error C Meta Path Unit Unit
  assembly : Assembly Os R H D B Poll Instant System Native Profiler
    Raw Listener TcpStream Error C Meta Path Unit Unit
  bootstrap : EvalBootstrap.Configuration Os × EvalBootstrap.Hooks
    (EvalExecutable.U Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
    C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
    CpuAffinity.Mask EvalSyncObjectAccess.Payload
    (ValidityMachine.Control (ThreadStacks.Storage
      (EvalWorld.World Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))) Os
  main : MainMachine.Hooks
    (EvalCallbackMachine.ThreadUser Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler)
    C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
    CpuAffinity.Mask ProgramExitPoll
  syncEffects : TypedSyncMachine.Effects
    (MachineHooks.State MiriMemoryKind
      (EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler))
  callbacks : EvalWindowsCallbackSourceConstruction.Product Os R EvalSyncObjectAccess.Payload H D
    (Other Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler
    C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
  callbackAssembly : EvalWindowsCallbackAssembly.Product Os R H D CpuAffinity.Mask B Poll
    Instant System Native Profiler Raw Listener TcpStream Error C ABI.ExternAbi
    (FnAbi TyId) (ArgAbi TyId)
  state : State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error

/-- Build the Windows execution package, construct its same-world raw foreign
assembly, attach bootstrap Main/TLS and source environment state, then derive
the backend-specific typed synchronization effects and actual callback router.
Every failure after a stateful operation returns the state prefix with error. -/
def startFromInitial
    {Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error ErrorHost Meta Path
      AddrIter : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (windowsHost : EvalWindowsEnvironmentConstruction.HostEffects
      (State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error) Os Error)
    (choice : C) (limits : ExecutionMachine.Limits)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (initial : State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error) :
    Except
      (State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error × StepError)
      (Started Os R H D B Poll Instant System Native Profiler C Raw Listener TcpStream Error
        ErrorHost Meta Path) := Id.run do
  let packageResult : Except StepError
      (ExecutionMachine.Config MiriMemoryKind
        (EvalConfigurationCore.SourceUser Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
          Poll Instant System Native Profiler Raw Listener TcpStream Error)
        C (Other Raw Listener TcpStream Error) ABI.ExternAbi Instant ×
       Context Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error C
        Meta Path Unit Unit) :=
    EvalWindowsConfigurationCore.makeFromSourcePackage
      (Os := Os) (R := R) (H := H) (D := D) (B := B) (Poll := Poll)
      (Instant := Instant) (System := System) (Native := Native) (Profiler := Profiler)
      (C := C) (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream) (Error := Error)
      (ErrorHost := ErrorHost) (Meta := Meta) (Path := Path) (AddrIter := AddrIter)
      (Zone := Unit) (Timestamp := Unit) prepared.compiler image bytes options
      sourceLeaves windowsHost choice options.callbackCapacity
  let package ← match packageResult with
    | .ok package => pure package
    | .error error => return .error (initial,error)
  let execution := package.1
  let context := package.2
  let some buildAssembly := context.sourceAssembly |
    return .error (initial,.unsupported "Windows source Core omitted its live assembly factory")
  let (afterAssembly,assemblyResult) := MachineHooks.run
    (ExecutionStateTransport.action (buildAssembly ())) initial
  let .ok (assembly : Assembly Os R H D B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C Meta Path Unit Unit) := assemblyResult |
    match assemblyResult with
    | .error error => return .error (afterAssembly,error)
    | .ok _ => return .error (afterAssembly,.unsupported "Windows source assembly result mismatch")
  let memory : EvalWindowsEnvironmentConstruction.Memory Os R
      EvalSyncPayload.Payload H D (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C := assembly.memory
  let bootstrapMemory : EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)) C
      EvalSyncObjectAccess.Payload := {
    access := memory.access
    allocation := memory.allocation
    deallocate := memory.deallocate
    pointers := memory.pointers
    projection := memory.projection
    arrays := memory.arrays
    symbolicAlignment := memory.symbolicAlignment
    enforceAlignment := memory.enforceAlignment
    stringScanBudget := memory.stringScanBudget
    choice := memory.choice
    pointerTy := memory.pointerTy
    pointerLayout := memory.pointerLayout }
  let bootstrapLift ← match EvalSourceRunConstruction.bootstrapFromSourceExecution
      (Os := Os) (R := R) (P := EvalSyncObjectAccess.Payload) (H := H) (D := D)
      (Aff := CpuAffinity.Mask) (B := B)
      (Poll := Poll) (Instant := Instant) (System := System) (Native := Native)
      (Profiler := Profiler) (C := C) prepared execution limits choice sourceLeaves.spans
      sourceLeaves.foreignSource.host.os sourceLeaves.foreignSource.host.environment
      bootstrapMemory bootstrapConfiguration afterAssembly with
    | .ok bootstrap => pure bootstrap.down
    | .error error => return .error (afterAssembly,error)
  let (afterInit,initResult) := MachineHooks.run
    (EvalBootstrap.createContextWithBytes bootstrapLift.2 bootstrapLift.1 choice) afterAssembly
  match initResult with
  | .error error => return .error (afterInit,error)
  | .ok _ => pure PUnit.unit
  let main := MainMachine.withTerminationPayload bootstrapLift.2.main
  let (callbackAssembly,afterCallbacks) ← match EvalWindowsCallbackAssembly.fromSource
      prepared.compiler prepared.image context assembly main sourceLeaves afterInit with
    | .ok result => pure result
    | .error (error,state) => return .error (state,error)
  let callbacks := callbackAssembly.callbacks
  let syncEffects := callbackAssembly.syncEffects
  return .ok ⟨execution,context,assembly,bootstrapLift,main,
    syncEffects,callbacks,callbackAssembly,afterCallbacks⟩

/-- Run an already constructed Windows world from its source-owned startup.
Each scheduler choice builds a fresh source configuration and connects its
foreign assembly to the same startup Main and callback registries. The
Windows loop then handles deadline, exit, join, and synchronization
callbacks without Unix descriptor callback seeds. -/
def runFromInitial
    {Os R H D B Poll Instant System Native Profiler C : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (windowsHost : EvalWindowsEnvironmentConstruction.HostEffects
      (State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error) Os Error)
    (pathToOs : Path → Os)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C)
    (initial : State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error) :
    Except StepError
      (EvalRunConstruction.RunResult
        (State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error)) := Id.run do
  if initialConfiguration.geometry.pageSize != sourceLeaves.foreignSource.geometry.pageSize ||
      initialConfiguration.geometry.stackAddress != sourceLeaves.foreignSource.geometry.stackAddress ||
      initialConfiguration.geometry.stackSize != sourceLeaves.foreignSource.geometry.stackSize ||
      initialConfiguration.alignment != sourceLeaves.foreignSource.alignment then
    return .ok (EvalRunConstruction.classifyError initial
      (.invalidProgram "initial machine geometry/alignment differs from Windows source Core inputs"))
  if sourceLeaves.hostConfiguration.communicate != bootstrapConfiguration.communicate then
    return .ok (EvalRunConstruction.classifyError initial
      (.invalidProgram "Windows startup and HostRuntime communication settings differ"))
  let startedResult := startFromInitial prepared image bytes options sourceLeaves windowsHost
    choice limits bootstrapConfiguration initial
  let .ok (started : Started Os R H D B Poll Instant System Native Profiler C Raw Listener
      TcpStream Error ErrorHost Meta Path) := startedResult |
    match startedResult with
    | .error (state,error) =>
      return .ok (EvalRunConstruction.classifyError state error)
    | .ok _ => return .ok (EvalRunConstruction.classifyError initial
        (.unsupported "Windows startup result mismatch"))
  let callbackAssembly : EvalWindowsCallbackAssembly.Product Os R H D CpuAffinity.Mask B Poll
      Instant System Native Profiler Raw Listener TcpStream Error C ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) := started.callbackAssembly
  let process : EvalRunConstruction.ProcessEffects
      (State Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    interrupted := fun state => sourceLeaves.foreignSource.host.process.interrupted
      (ExecutionStateTransport.inward state)
    handleAbnormalTermination := fun state => ExecutionStateTransport.outward
      (sourceLeaves.foreignSource.host.process.handleAbnormalTermination
        (ExecutionStateTransport.inward state)) }
  let clock := EvalSourceRunConstruction.sourceClockToOuter
    sourceLeaves.foreignSource.host.clock
  let durationSince := EvalSourceRunConstruction.sourceDurationSinceToOuter
    sourceLeaves.foreignSource.host.systemDurationSince
  let choiceAccess := EvalSourceRunConstruction.sourceChoiceAccess
    (Os := Os) (R := R) (H := H) (D := D) (O := Other Raw Listener TcpStream Error)
    (Aff := CpuAffinity.Mask) (B := B) (Poll := Poll) (Instant := Instant)
    (System := System) (Native := Native) (Profiler := Profiler)
    (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream) (Error := Error)
  let configs : C → Except StepError (EvalExecutable.Core Os R EvalSyncPayload.Payload H D
      (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant) :=
    fun selected => do
      let connection :
          EvalWindowsConfigurationCore.Context Os R H D B Poll Instant System Native Profiler
            C Raw Listener TcpStream Error Meta Path callbackAssembly.Zone
            callbackAssembly.Timestamp →
          Assembly Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error
            C Meta Path callbackAssembly.Zone callbackAssembly.Timestamp →
          EStateM StepError
            (EvalWindowsCallDispatchConstruction.CoreState Os R H D CpuAffinity.Mask B Poll
              Instant System Native Profiler Raw Listener TcpStream Error)
            (Assembly Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error
            C Meta Path callbackAssembly.Zone callbackAssembly.Timestamp) :=
        fun context assembly => do
        let unwindInner := EvalCallRuntime.unwind context.access context.projection
          context.functions options.panicUnwinds context.callFunction
        EvalWindowsConnectedSourceAssembly.connectFromSource
          (Zone := callbackAssembly.Zone) (Timestamp := callbackAssembly.Timestamp)
          prepared.compiler options sourceLeaves
          started.main callbackAssembly pathToOs
          (ExecutionForeignTransport.unwind unwindInner) context assembly
      let portableConnection := fun
          (context : EvalWindowsConfigurationCore.Context Os R H D B Poll Instant System Native Profiler
            C Raw Listener TcpStream Error Meta Path callbackAssembly.Zone callbackAssembly.Timestamp)
          (foreign : ForeignItems.Hooks Provenance
            (EvalWindowsCallDispatchConstruction.CoreState Os R H D CpuAffinity.Mask B Poll
              Instant System Native Profiler Raw Listener TcpStream Error)
            (RuntimePlace Provenance) (RuntimePlace Provenance)
            (Pointer (Option Provenance)) LoadedBody CallInstance) => do
        let rawMemory ← match EvalConfigurationCore.environmentMemoryFromCore prepared.compiler
            context.access context.allocation context.extras context.deallocationDiagnostic
            context.nativeDrop context.pointers context.spans context.projection context.choice
            sourceLeaves.foreignSource.alignment sourceLeaves.foreignSource.stringScanBudget with
          | .ok memory => pure memory
          | .error error => throw error
        let memory : EvalHostRuntimeConstruction.EnvironmentMemory
            (ValidityMachine.Control (EvalCoreMachine.Stored Os R EvalSyncPayload.Payload H D
              (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
              (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)))
            C EvalSyncPayload.Payload := {
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
        let baseEffects := EvalMiriHostEffectsConstruction.fromCoreSource
          sourceLeaves.foreignSource.host.os memory
          sourceLeaves.foreignSource.host.hostFiles
          sourceLeaves.hostConfiguration.communicate options.miriWriteRetryBudget
          (some (EvalMiriHostEffectsConstruction.sourceAllocIdNumberFromImage image))
        let machine := EvalMiriSourceConstruction.fromContext options context
        let effects := {baseEffects with
          namePointer := EvalMiriTreeDiagnostics.namePointer machine
            (baseEffects.writeHost true)
          printBorrowState := EvalMiriTreeDiagnostics.printBorrowState machine
            (baseEffects.writeHost true) image}
        let unitLayout : MachineHooks.M MiriMemoryKind
            (EvalCoreMachine.User Os R EvalSyncPayload.Payload H D
              (Other Raw Listener TcpStream Error) CpuAffinity.Mask B
              (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
            LocalLayout := do
          match CompilerFacts.unitLayout
              prepared.compiler.lifecycle.calls.symbols.facts.context with
          | .ok value => pure ⟨value.ty,value.layout⟩
          | .error reason =>
            throw (.unsupported s!"compiler unit layout for Windows Miri thread shim: {reason}")
        pure (EvalMiriSourceRuntime.bindPhysical machine context.choice
          started.main.termination.tls.thread unitLayout none effects foreign)
      let package ← EvalWindowsConfigurationCore.makeWithSourceConnection
        (Zone := callbackAssembly.Zone) (Timestamp := callbackAssembly.Timestamp)
        prepared.compiler image bytes options sourceLeaves windowsHost selected capacity
        (some connection) (some portableConnection)
      pure package.1
  let hostConfiguration := sourceLeaves.hostConfiguration
  let loop := EvalWindowsRunConstruction.hooks hostConfiguration
    started.callbacks configs limits choiceAccess clock durationSince process
  return .ok (EvalWindowsRunConstruction.runUntilTerminal loop iterationFuel
    outerChoices started.state)

end Miri.Input.EvalWindowsSourceRunConstruction
