import Miri.Input.EvalWindowsRawSourceEntry
import Miri.Input.EvalSourceRunFinalization

/-! Windows source-facing process completion. The Windows raw entry shares
the canonical machine state and post-exit policy; retain its low-level
RunResult API while providing a source entry that performs real leak checks. -/
namespace Miri.Input.EvalWindowsSourceRunFinalization
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- Windows raw-host startup and MIR execution followed by the same
canonical thread and reachable-allocation finalization used by Unix. Reporting
and the ignore-leaks setting remain explicit host capabilities. -/
def runFromSourceAndFinalize
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
    (outerChoices : List C)
    (ignoreLeaks : Bool)
    (reports : EvalSourceRunFinalization.ReportEffects Os R
      EvalSyncPayload.Payload H D
      (EvalWindowsSourceRunConstruction.Other Raw Listener TcpStream Error)
      CpuAffinity.Mask B Poll Instant System Native Profiler) :
    EStateM StepError External
      (EvalSourceRunFinalization.Result
        (EvalWindowsSourceRunConstruction.State Os R H D B Poll Instant System Native Profiler
          Raw Listener TcpStream Error)) := do
  let result ← EvalWindowsRawSourceEntry.runFromSource prepared bytes options sourceLeaves
    windowsHost pathToOs choice initialConfiguration initialMemory runtimeTypes choiceTape
    hostRuntime bootstrapConfiguration limits capacity iterationFuel outerChoices
  pure (EvalSourceRunFinalization.finishResult reports ignoreLeaks result)

end Miri.Input.EvalWindowsSourceRunFinalization
