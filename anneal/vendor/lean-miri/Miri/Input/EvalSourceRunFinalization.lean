import Lean.Util.Profile
import Miri.Input.EvalSourceRunConstruction
import Miri.Interpreter.EntryResult

/-! Canonical source process completion. The low-level bounded runner
continues to expose `RunResult`; this module applies eval.rs's final thread and
memory leak policy to real source exits before a source-facing caller receives
the exit status. Diagnostics remain explicit host effects. -/
namespace Miri.Input.EvalSourceRunFinalization
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev SourceState Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalRuntimeConstruction.EntryState Os R P H D O Aff B
    (EvalSourceRunConstruction.SourceHost Poll Instant System H D O Native Profiler)
abbrev SourceOuter Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalRuntimeConstruction.EntryOuter Os R P H D O Aff B
    (EvalSourceRunConstruction.SourceHost Poll Instant System H D O Native Profiler)

set_option autoImplicit false in
structure ReportEffects
    (Os R P H D O Aff B Poll Instant System Native Profiler : Type) where
  reportThreadLeak : MachineHooks.M MiriMemoryKind
    (SourceOuter Os R P H D O Aff B Poll Instant System Native Profiler) Unit
  reportLeaks : EntryResult.Leaks → MachineHooks.M MiriMemoryKind
    (SourceOuter Os R P H D O Aff B Poll Instant System Native Profiler) Unit
  ignoreLeaksNote : MachineHooks.M MiriMemoryKind
    (SourceOuter Os R P H D O Aff B Poll Instant System Native Profiler) Unit
  failureCode : Int32

inductive Result (S : Type) where
  | finished (state : S) (exitCode : Int32)
  | undefinedBehavior (state : S) (error : StepError)
  | unsupported (state : S) (error : StepError)
  | failed (state : S) (error : StepError)
  | pending (state : S) (cause : EvalRunConstruction.PendingCause)
  deriving Repr

private def staticRoots
    (user : SourceOuter Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
      Aff B Poll Instant System Native Profiler) : Array AllocId :=
  user.user.payload.payload.runtime.tls.staticRoots

private def entryHooks
    (reports : ReportEffects Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
      Aff B Poll Instant System Native Profiler)
    (exitCode : Int32) (leakCheck : Bool) : EntryResult.Hooks
      (SourceOuter Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
        Aff B Poll Instant System Native Profiler) := {
  reportResult := fun _ => pure (some (exitCode,leakCheck))
  staticRoots := staticRoots
  reportThreadLeak := reports.reportThreadLeak
  reportLeaks := reports.reportLeaks
  ignoreLeaksNote := reports.ignoreLeaksNote
  failureCode := reports.failureCode
}

private def classifyFinalizerError
    (state : EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
      Poll Instant System Native Profiler)
    (error : StepError) : Result
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        Poll Instant System Native Profiler) :=
  match EvalRunConstruction.classifyError state error with
  | .exited after _ _ => .failed after error
  | .undefinedBehavior after error => .undefinedBehavior after error
  | .unsupported after error => .unsupported after error
  | .failed after error => .failed after error
  | .pending after cause => .pending after cause

/-- Apply the pinned post-exit policy to an actual exited machine state. The
thread status, TLS static roots and allocation graph come from that state;
only diagnostic output and the ignore-leaks setting remain host capabilities.
Pending and non-exit outcomes retain their original classification. -/
def finishResultProfiled
    (profile : Lean.Options)
    (reports : ReportEffects Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
      Aff B Poll Instant System Native Profiler)
    (ignoreLeaks : Bool)
    (result : EvalRunConstruction.RunResult
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        Poll Instant System Native Profiler)) : Result
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        Poll Instant System Native Profiler) := Id.run do
  match result with
  | .exited state code leakCheck =>
      let exitCode := Int32.ofInt code
      let (after, outcome) := MachineHooks.run
        (EntryResult.finishProfiled profile (entryHooks reports exitCode leakCheck) ignoreLeaks
          (.termination (.exit code leakCheck))) state
      match outcome with
      | .ok finalCode => return .finished after finalCode
      | .error error => return classifyFinalizerError after error
  | .undefinedBehavior state error => .undefinedBehavior state error
  | .unsupported state error => .unsupported state error
  | .failed state error => .failed state error
  | .pending state cause => .pending state cause

def finishResult
    (reports : ReportEffects Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
      Aff B Poll Instant System Native Profiler)
    (ignoreLeaks : Bool)
    (result : EvalRunConstruction.RunResult
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        Poll Instant System Native Profiler)) : Result
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        Poll Instant System Native Profiler) :=
  finishResultProfiled {} reports ignoreLeaks result

theorem finishResultProfiled_eq_finishResult
    (profile : Lean.Options)
    (reports : ReportEffects Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
      Aff B Poll Instant System Native Profiler)
    (ignoreLeaks : Bool)
    (result : EvalRunConstruction.RunResult
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        Poll Instant System Native Profiler)) :
    finishResultProfiled profile reports ignoreLeaks result =
      finishResult reports ignoreLeaks result := by
  rfl

/-- Full raw-host entry followed by Miri's source exit finalizer.
Unlike `runFromSource`, this source-facing API returns an exit code only after
thread-leak and reachable-allocation checks have run on the actual terminal
World. The lower-level runner remains available to composed callers. -/
def runFromSourceAndFinalizeProfiled
    {Os R H D B Poll Instant System Native Profiler C External : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (profile : Lean.Options)
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant EvalSyncObjectAccess.Payload AddrIter)
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
    (reports : ReportEffects Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      Poll Instant System Native Profiler)
    (stableChoice : Option (EvalSourceRunConstruction.StableChoice choice) := none) :
    EStateM StepError External (Result
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        Poll Instant System Native Profiler)) := do
  let result ← EvalSourceRunConstruction.runFromSourceProfiled profile prepared image bytes options
    sourceLeaves choice initialConfiguration initialMemory runtimeTypes choiceTape hostRuntime
    bootstrapConfiguration limits capacity iterationFuel outerChoices true stableChoice
  let label := match result with
    | .exited _ code leakCheck => s!"finalization.raw_result.exited.code_{code}.leak_{leakCheck}"
    | .undefinedBehavior .. => "finalization.raw_result.undefined_behavior"
    | .unsupported .. => "finalization.raw_result.unsupported"
    | .failed .. => "finalization.raw_result.failed"
    | .pending .. => "finalization.raw_result.pending"
  let result := Lean.profileit label profile (fun _ => result)
  let result := Lean.profileit "finalization.start" profile (fun _ => result)
  pure (Lean.profileit "finalization.complete" profile fun _ =>
    finishResultProfiled profile reports ignoreLeaks result)

/-- Compatibility entry with the original positional API. Profiling is opt-in
through `runFromSourceAndFinalizeProfiled`; this entry preserves all old calls. -/
def runFromSourceAndFinalize
    {Os R H D B Poll Instant System Native Profiler C External : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
      ErrorHost Meta Path Miri.MIR.Place C Instant EvalSyncObjectAccess.Payload AddrIter)
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
    (reports : ReportEffects Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      Poll Instant System Native Profiler)
    (stableChoice : Option (EvalSourceRunConstruction.StableChoice choice) := none) :
    EStateM StepError External (Result
      (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
        Poll Instant System Native Profiler)) :=
  runFromSourceAndFinalizeProfiled {} prepared image bytes options sourceLeaves choice
    initialConfiguration initialMemory runtimeTypes choiceTape hostRuntime bootstrapConfiguration
    limits capacity iterationFuel outerChoices ignoreLeaks reports stableChoice

end Miri.Input.EvalSourceRunFinalization
