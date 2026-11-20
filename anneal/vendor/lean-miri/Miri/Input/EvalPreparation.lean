import Miri.Input.EvalEntryMachine
import Miri.Input.CompilerGlobals
import Miri.Input.CompilerContextSpan
import Miri.Input.CompilerAllocIdWorld
import Miri.Input.Decoder

/-! Initial compiler/image preparation for the canonical entry machine. The
allocation import is deliberately not hidden in Except: failed registration
retains the consumed allocation identities and successfully imported prefix. -/
namespace Miri.Input.EvalPreparation
open Lean Miri.Memory Miri.Interpreter
structure Prepared where
  compiler : CompilerProviders.Prepared
  image : AllocationImage.Imported
  types : RuntimeArrayTypes.World
  layouts : EvalEntryMachine.Layouts
  dummySpan : Miri.MIR.SpanRef

structure Attempt where
  memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
  outcome : Except String Prepared

/-- Compiler table preparation precedes allocation registration. All consumers
share its final identity tables; graph definitions may not be appended only to
an isolated image view. Primitive layouts and the persistent runtime type world
are required evidence, never inferred from storage sizes. -/
def prepareProfiled (profile : Lean.Options) (input : LoweredProgram) : Attempt := Id.run do
  let empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind := .empty
  match profileit "preparation.eval.validate_alloc_id_world" profile fun _ =>
      Miri.Input.validateCompilerAllocIdWorldRaw input.input.raw input.input.allocations
        input.input.compilerAllocIdWorld with
  | .ok _ => pure ()
  | .error error => return ⟨empty,.error s!"compiler AllocId world: {error}"⟩
  let preparedInput := profileit "preparation.eval.compiler_globals" profile fun _ =>
    CompilerGlobals.prepareProgram input
  let compilerResult := profileit "preparation.eval.providers" profile fun _ =>
    CompilerProviders.prepareProfiled profile preparedInput
  let compiler ← match compilerResult with
    | .ok value => pure value
    | .error error => return ⟨empty,.error error⟩
  let dummySpanResult := profileit "preparation.eval.root_span" profile fun _ =>
    CompilerContextSpan.rootSpan compiler.program
  let dummySpan ← match dummySpanResult with
    | .ok value => pure value
    | .error error => return ⟨empty,.error error⟩
  let layoutsResult := profileit "preparation.eval.layouts" profile fun _ =>
    EvalEntryMachine.layouts compiler
  let layouts ← match layoutsResult with
    | .ok value => pure value
    | .error error => return ⟨empty,.error error⟩
  let types ← match profileit "preparation.eval.initial_arrays" profile fun _ => compiler.initialArrays with
    | .ok value => pure value
    | .error error => return ⟨empty,.error error⟩
  let importNodes := match compiler.program.input.compilerAllocIdWorld with
    | none => compiler.program.input.allocations
    | some _ => compiler.program.input.allocations.filter (·.status == .supported)
  let imported := profileit "preparation.eval.allocation_import_graph" profile fun _ =>
    AllocationImage.importGraph compiler.runtime.target
      compiler.program.compilerTables.definitions CompilerGlobals.queries importNodes empty
  match imported.outcome with
  | .error error => return ⟨imported.memory,.error error⟩
  | .ok image =>
    let memory ← match profileit "preparation.eval.install_alloc_id_world" profile fun _ =>
        CompilerAllocIdWorld.install compiler.program.input.raw
          compiler.program.input.compilerAllocIdWorld compiler.program.input.allocations imported.memory with
      | .ok value => pure value
      | .error error => return ⟨imported.memory,.error s!"compiler AllocId world: {error}"⟩
    return ⟨memory,.ok ⟨compiler,image,types,layouts,dummySpan⟩⟩

def prepare (input : LoweredProgram) : Attempt :=
  prepareProfiled {} input

/-- Profiling only observes preparation boundaries and leaves every returned
memory state and strict error unchanged. -/
theorem prepareProfiled_eq_prepare (profile : Lean.Options) (input : LoweredProgram) :
    prepareProfiled profile input = prepare input := by
  rfl
end Miri.Input.EvalPreparation
