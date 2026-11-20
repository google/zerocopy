import Miri.Input.EvalWindowsSourceRunConstruction
import Miri.Input.EvalPreparation
import Miri.Input.EvalStartupRuntimeConstruction
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.MachineConstruction

/-! Raw-host Windows process entry. Construct the canonical World once from
the imported memory, runtime types, choice tape and HostRuntime lifecycle, then
continue through the source-owned Windows startup and ordinary MIR runner. -/
namespace Miri.Input.EvalWindowsRawSourceEntry
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option autoImplicit false in
def runFromSource
    {Os R H D B Poll Instant System Native Profiler C External : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (prepared : EvalPreparation.Prepared)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant CallInstance AddrIter)
    (windowsHost : EvalWindowsEnvironmentConstruction.HostEffects
      (EvalWindowsSourceRunConstruction.State Os R H D B Poll Instant System Native Profiler
        Raw Listener TcpStream Error) Os Error)
    (pathToOs : Path → Os)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (runtimeTypes : RuntimeArrayTypes.World)
    (choiceTape : ExecutionChoices.Tape)
    (hostRuntime : HostRuntime.Hooks External Poll Instant System Native Profiler)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C) :
    EStateM StepError External
      (EvalRunConstruction.RunResult
        (EvalWindowsSourceRunConstruction.State Os R H D B Poll Instant System Native Profiler
          Raw Listener TcpStream Error)) := do
  let compiler := prepared.compiler
  let targetFacts ← match compiler.externStatics.targetFacts with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"compiler target facts unavailable: {reason}")
  unless targetFacts.os == "windows" do
    throw (.invalidProgram s!"Windows raw source entry requested for `{targetFacts.os}`")
  let startupFacts ← match EvalStartupRuntimeConstruction.prepare compiler with
    | .ok facts => pure facts
    | .error reason => throw (.unsupported s!"compiler startup facts: {reason}")
  let noCore ← match startupFacts.noCore with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler no_core query: {reason}")
  let cULong ← match CompilerPrimitiveFacts.cULongLayout compiler.runtime with
    | .ok layout => pure layout
    | .error reason => throw (.unsupported s!"compiler c_ulong layout: {reason}")
  let machineTarget : MachineConstruction.Target := {
    os := targetFacts.os
    noCore
    cpuCount := sourceLeaves.foreignSource.host.unixConfig.numCpus
    cUlongBytes := cULong.layout.size.bytes.toNat
    endian := compiler.runtime.target.base.endian }
  let initial ← MachineConstruction.create hostRuntime sourceLeaves.hostConfiguration
    machineTarget initialConfiguration initialMemory runtimeTypes choiceTape
  match EvalWindowsSourceRunConstruction.runFromInitial prepared prepared.image bytes options
      sourceLeaves windowsHost pathToOs choice initialConfiguration bootstrapConfiguration limits
      capacity iterationFuel outerChoices initial with
  | .ok result => pure result
  | .error error => throw error

end Miri.Input.EvalWindowsRawSourceEntry
