import Miri.Input.CompilerLifecycle
import Miri.Input.CompilerBacktraceSource
import Miri.Input.CompilerBacktraceFacts
import Miri.Input.CompilerFrameMetadata
import Miri.Input.CompilerInstanceAbi

/-! One final compilation-local identity table for actual frame lifecycle,
full-instance ABI and backtrace source queries. Appending span/definition IDs
never invalidates already prepared runtime dictionaries. -/
namespace Miri.Input.CompilerLifecyclePipeline
open Lean Miri.ABI Miri.Memory Miri.Interpreter
structure Prepared where
  calls : CompilerCallPipeline.Prepared
  instances : CompilerInstanceAbi.Prepared
  lifecycle : CompilerLifecycle.Prepared
  backtrace : CompilerBacktraceSource.Prepared
  frames : CompilerFrameMetadata.Prepared
  shim : CompilerShimAbi.Prepared

private def rebind (p : CompilerCallPipeline.Prepared) (program : LoweredProgram) :
    CompilerCallPipeline.Prepared :=
  {p with
    calls := {p.calls with program}
    scopes := {p.scopes with program}
    runtime := {p.runtime with program}
    symbols := {p.symbols with facts := {p.symbols.facts with
      context := p.symbols.facts.context.withProgram program}}}

def prepareProfiled (profile : Lean.Options) (calls : CompilerCallPipeline.Prepared) : Except String Prepared := do
  let runtime := calls.calls.runtime
  let instances ← profileit "preparation.lifecycle.instance_abi" profile fun _ =>
    CompilerInstanceAbi.prepare runtime calls.calls.program
      (some calls.sourceEquality) (some calls.calls.functionAbiCache)
  let lifecycle := profileit "preparation.lifecycle.compiler_lifecycle" profile fun _ =>
    CompilerLifecycle.prepare instances.program
  let backtrace ← profileit "preparation.lifecycle.backtrace_source" profile fun _ =>
    CompilerBacktraceSource.prepare lifecycle.program
  let program := backtrace.program
  let calls := profileit "preparation.lifecycle.rebind_calls" profile fun _ => rebind calls program
  let frames ← profileit "preparation.lifecycle.frame_metadata" profile fun _ =>
    CompilerFrameMetadata.prepare calls
  let shim ← profileit "preparation.lifecycle.shim_abi" profile fun _ =>
    CompilerShimAbi.prepare runtime (some calls.calls.functionAbiCache)
  return ⟨calls,{instances with program},{lifecycle with program},backtrace,frames,shim⟩

def prepare (calls : CompilerCallPipeline.Prepared) : Except String Prepared :=
  prepareProfiled {} calls

/-- Profiling wrappers preserve the lifecycle preparation result exactly. -/
theorem prepareProfiled_eq_prepare (profile : Lean.Options)
    (calls : CompilerCallPipeline.Prepared) :
    prepareProfiled profile calls = prepare calls := by
  rfl

/-- Close all frame compiler leaves with actual exported query results. The
remaining fields concern machine memory, ghost identity allocation and unwind. -/
def lifecycleHooks (p : Prepared) (userRelevantCrates : Array Nat)
    (base : CallMachine.Lifecycle K User C) : CallMachine.Lifecycle K User C :=
  CompilerLifecycle.hooks p.lifecycle {base with
    compiler := CompilerFrameMetadata.hooks p.frames userRelevantCrates}

/-- Source query closure composes with BacktraceMachine's actual memory binding.
Actual function allocation/address/provenance lookup remains the machine's job. -/
def backtraceHooks (p : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState P Extra K)
    (base : Backtrace.Hooks P S D MD B I E CompilerBacktraceSource.Position) :
    Backtrace.Hooks P S D MD B I E CompilerBacktraceSource.Position :=
  CompilerBacktraceSource.hooks p.backtrace
    (CompilerBacktraceFacts.hooks p.calls p.shim image memory base)

/-- Root/direct/virtual/drop calls share exact full-instance/extra-argument ABI
queries and exact LoadedBody identities from this same final table. -/
def functionHooks (p : Prepared)
    (base : FunctionCalls.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    FunctionCalls.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  CompilerCallPipeline.bindFunctionCalls p.calls
    {base with call := CompilerInstanceAbi.hooks p.instances base.call}
end Miri.Input.CompilerLifecyclePipeline
