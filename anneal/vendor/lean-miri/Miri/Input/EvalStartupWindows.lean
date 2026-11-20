import Miri.Input.EvalStartupRuntimeConstruction
import Miri.Input.CompilerWindowsConstants

/-! Exact eval_windows compiler constants at the TLS callback boundary.
The source requests a particular module/name pair only on the Windows callback
path. Missing rows and unsupported constants therefore remain demand-time
Unknowns, while every successful value is decoded from the canonical named
constant table with its exported type/layout checks. -/
namespace Miri.Input.EvalStartupWindows
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Outer Os R P H D O Aff B Host :=
  EvalRuntimeConstruction.EntryOuter Os R P H D O Aff B Host

private def demand (value : Except String (Scalar Provenance)) :
    MachineHooks.M MiriMemoryKind (Outer Os R P H D O Aff B Host) (Scalar Provenance) :=
  match value with
  | .ok scalar => pure scalar
  | .error reason => throw (.unsupported reason)

/-- Source-backed `eval_windows(lib, name)`. In the pinned TLS path `lib` is
the exact module component below `std::sys::pal::windows`; it is not matched by
suffix or display name. -/
def evalWindows (compiler : CompilerProviders.Prepared) :
    String → String → MachineHooks.M MiriMemoryKind
      (Outer Os R P H D O Aff B Host) (Scalar Provenance) :=
  fun module name => demand (CompilerWindowsConstants.scalar compiler.namedConstants module name)

/-- Main/TLS assembly with the exact compiler-backed Windows constant leaf.
All other capabilities remain the ones already derived from the same fixed
execution Config and actual machine state. -/
def mainFromExecution
    (compiler : CompilerProviders.Prepared)
    (execution : ExecutionMachine.Config MiriMemoryKind
      (EvalEntryMachine.InnerUser Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost)
    (limits : ExecutionMachine.Limits)
    (deallocationError : MemoryLifecycleError → StepError)
    (deallocate : Pointer (Option Provenance) → Option (Size × Align) →
      MemoryKind MiriMemoryKind → MachineHooks.M MiriMemoryKind
        (EvalEntryMachine.InnerUser Os R P H D O Aff B Host) Unit)
    (choice : C) (layout : EvalEntryMachine.Layouts)
    (spans : AllocationDriver.SpanHooks) (platform : TlsPlatform)
    (format : ConstructorBinaryFormat)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind
      (Outer Os R P H D O Aff B Host) (Pointer Provenance))
    (state : MachineHooks.State MiriMemoryKind (Outer Os R P H D O Aff B Host)) :=
  EvalEntryMachine.mainFromExecution compiler execution limits deallocationError deallocate
    choice layout spans platform format externStatic (evalWindows compiler) state

end Miri.Input.EvalStartupWindows
