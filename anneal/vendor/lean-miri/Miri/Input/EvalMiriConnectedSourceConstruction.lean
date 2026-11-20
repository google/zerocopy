import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalMiriSourceConstruction
import Miri.Input.EvalMiriHostEffectsConstruction
import Miri.Input.EvalMiriSourceRuntime
import Miri.Input.EvalMiriTreeDiagnostics
import Miri.Input.AllocationImage
import Miri.Input.CompilerFacts
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.ExecutionChoiceBindings

/-! Connect source-built physical Miri operations to a selected Core's
portable foreign resolver. The Miri machine, thread machine, host capabilities,
compiler queries, and environment memory all come from this exact source
configuration and callback package. -/
namespace Miri.Input.EvalMiriConnectedSourceConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalConfigurationCore.SourceOther Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalCoreMachine.State Os R P H D O Aff B Host
abbrev World Os R P H D O Aff B Host := EvalWorld.World Os R P H D O Aff B Host
abbrev Stored Os R P H D O Aff B Host := EvalCoreMachine.Stored Os R P H D O Aff B Host
abbrev Control Os R P H D O Aff B Host := ValidityMachine.Control (Stored Os R P H D O Aff B Host)
abbrev EntryUser Os R P H D O Aff B Host := ValidityMachine.UserState (World Os R P H D O Aff B Host)

private def liftCompiler {Os R P H D O Aff B Host A : Type}
    (value : Except String A) :
    MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A :=
  match value with
  | .ok result => pure result
  | .error reason => throw (.unsupported s!"compiler query: {reason}")

/-- Install Miri on the selected, already callback-rebound Core configuration.
The supplied thread hooks are projected from the same source Main package;
Miri spawn/join therefore share its actual TLS, scheduler, and return behavior. -/
def bind [DecidableEq MiriMemoryKind]
    {Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost
      Meta Path C ClockHost I AddrIter Assembly : Type}
    (p : CompilerProviders.Prepared)
    (image : AllocationImage.Imported)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D
      Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path Place C
      ClockHost I AddrIter)
    (context : EvalConfigurationCore.ForeignContext Os R EvalSyncObjectAccess.Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
      C ClockHost Assembly)
    (thread : ThreadMachine.Hooks MiriMemoryKind
      (EntryUser Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C (Other Raw Listener TcpStream Error) ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff)
    (foreign : ForeignItems.Hooks Provenance
      (State Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    Except StepError (ForeignItems.Hooks Provenance
      (State Os R EvalSyncObjectAccess.Payload H D
        (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) := do
  let memory ← EvalConfigurationCore.environmentMemoryFromCore p context.access context.allocation
    context.extras context.deallocationDiagnostic context.nativeDrop context.pointers context.spans
    context.projection context.choice sourceLeaves.foreignSource.alignment
    sourceLeaves.foreignSource.stringScanBudget
  let machine := EvalMiriSourceConstruction.fromContext options context
  let unitLayout := liftCompiler
    ((CompilerFacts.unitLayout context.prepared.lifecycle.calls.symbols.facts.context).map
      fun value => ⟨value.ty,value.layout⟩)
  let threadChoices : ExecutionChoices.Access
      (ThreadMachine.State MiriMemoryKind
        (EntryUser Os R EvalSyncObjectAccess.Payload H D
          (Other Raw Listener TcpStream Error) Aff B
          (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))) := {
    get := fun state => state.machine.user.user.payload.payload.choices
    put := fun state tape => {state with machine := {state.machine with user :=
      {state.machine.user with user := {state.machine.user.user with payload :=
        {state.machine.user.user.payload with payload :=
          {state.machine.user.user.payload.payload with choices := tape}}}}}}}
  let thread := ExecutionChoiceBindings.threadClockReuse threadChoices thread
  let writeStderr := fun bytes => EvalMiriHostEffectsConstruction.writeAllHost
    (sourceLeaves.foreignSource.host.hostFiles.hostWrite .stderr)
    options.miriWriteRetryBudget bytes
  let effects := EvalMiriHostEffectsConstruction.fromCoreSource
    sourceLeaves.foreignSource.host.os memory sourceLeaves.foreignSource.host.hostFiles
    sourceLeaves.hostConfiguration.communicate options.miriWriteRetryBudget
    (sourceAllocIdNumber := some
      (EvalMiriHostEffectsConstruction.sourceAllocIdNumberFromImage image))
        (namePointer := some (EvalMiriTreeDiagnostics.namePointer machine writeStderr))
    (printBorrowState := some fun raw showUnnamed =>
      EvalMiriTreeDiagnostics.printBorrowState machine writeStderr image raw showUnnamed)
  return EvalMiriSourceRuntime.bindPhysical machine context.choice thread unitLayout none effects foreign

end Miri.Input.EvalMiriConnectedSourceConstruction
