import Miri.Input.CompilerConstantMachine
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.OperandPath

/-! Ordinary operand constants use their exact structural position in the
current instruction. Repeated equal constants retain distinct query sites.
No span, value, or evaluation-counter search participates in site selection. -/
namespace Miri.Input.CompilerOperandSites
open Miri.Interpreter Miri.Memory

def current (path : OperandPath) : MachineHooks.M K User CompilerConstantQueries.Site := do
  let frame ← MachineHooks.currentFrame
  let .mir location := frame.location | throw .expectedMirLocation
  return ⟨frame.bodyIdentity.index, location, path.map fun element => match element with
    | .field name => .field name
    | .index index => .index index⟩

/-- Install production constant evaluation. The erased legacy callback is
explicitly rejected so accidentally dropping a structural path cannot succeed. -/
def hooks (prepared : CompilerConstantQueries.Prepared) (runtime : RuntimeMetadata)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classify : ConstantError → StepError) (debugAssertions : Bool)
    (operands : OperandMachine.Hooks K User C) : OperandMachine.Hooks K User C :=
  {operands with
    constant := fun _ _ _ => throw (.unsupported "constant operand requires an exact structural source site")
    constantAt := fun _ path constant known => do
      let site ← current path
      CompilerConstantMachine.evalAt prepared runtime site functions arithmetic externStatic classify constant known
        (if debugAssertions then some (fun computed expected =>
          match operands.layoutCompatible computed expected with
          | .ok value => pure value
          | .error error => throw error) else none)}

/-- Source-bound variant for providers that retain their exact compatibility
binding across Core reconstruction. -/
def hooksBound {prepared : CompilerConstantQueries.Prepared} {runtime : RuntimeMetadata}
    (binding : CompilerConstantQueries.Binding prepared runtime)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classify : ConstantError → StepError) (debugAssertions : Bool)
    (operands : OperandMachine.Hooks K User C) : OperandMachine.Hooks K User C :=
  {operands with
    constant := fun _ _ _ => throw (.unsupported "constant operand requires an exact structural source site")
    constantAt := fun _ path constant known => do
      let site ← current path
      CompilerConstantMachine.evalAtBound binding site functions arithmetic externStatic classify constant known
        (if debugAssertions then some (fun computed expected =>
          match operands.layoutCompatible computed expected with
          | .ok value => pure value
          | .error error => throw error) else none)}

/-- Attach after the compiler/function-provider dictionary so imported pointer
constants use exactly its canonical allocation/provenance registry. -/
def executionHooks (prepared : CompilerConstantQueries.Prepared) (runtime : RuntimeMetadata)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classify : ConstantError → StepError)
    (config : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {config with operands := {config.operands with
    constantAt := fun _ path constant known => do
      let site ← current path
      CompilerConstantMachine.evalAt prepared runtime site config.functions config.arithmetic externStatic classify constant known
        (if config.compiler.debugAssertions then some (fun computed expected =>
          match config.copy.compatible computed expected with
          | .ok value => pure value
          | .error error => throw error) else none)}}

/-- Attach the retained source binding after compiler/function provider
construction, without rechecking the prepared/runtime JSON documents. -/
def executionHooksBound {prepared : CompilerConstantQueries.Prepared} {runtime : RuntimeMetadata}
    (binding : CompilerConstantQueries.Binding prepared runtime)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classify : ConstantError → StepError)
    (config : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {config with operands := {config.operands with
    constantAt := fun _ path constant known => do
      let site ← current path
      CompilerConstantMachine.evalAtBound binding site config.functions config.arithmetic externStatic classify constant known
        (if config.compiler.debugAssertions then some (fun computed expected =>
          match config.copy.compatible computed expected with
          | .ok value => pure value
          | .error error => throw error) else none)}}

end Miri.Input.CompilerOperandSites
