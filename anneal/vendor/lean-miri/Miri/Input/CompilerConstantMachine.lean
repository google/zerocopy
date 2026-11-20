import Miri.Input.CompilerConstantQueries
import Miri.Interpreter.ConstantMachine

/-! Exact compiler constant evidence and actual machine provenance/address
adjustment meet at the current source operand site, never by source-span search. -/
namespace Miri.Input.CompilerConstantMachine
open Miri.ABI Miri.Memory Miri.Interpreter

/-- Production variant using the compatibility result made during compiler
preparation. The binding indices retain the exact prepared/runtime values. -/
def evalOperandBound {prepared : CompilerConstantQueries.Prepared} {runtime : RuntimeMetadata}
    (binding : CompilerConstantQueries.Binding prepared runtime)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (base : ConstantMachine.Queries K User)
    (classifyConstantError : ConstantError → StepError)
    (constant : MIR.ConstOperand) : MachineHooks.M K User (OpTy Provenance) := do
  unless binding.compatible do
    throw (.invalidProgram "constant runtime/compiler evidence document mismatch")
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity.index == site.bodyIndex do
    throw (.invalidProgram "constant operand site belongs to another canonical body")
  unless frame.location == .mir site.location do
    throw (.invalidProgram "constant operand site differs from current MIR location")
  let compiler := CompilerConstantQueries.queriesAt prepared site base
  let actual := ConstantMachine.queries functions arithmetic externStatic compiler
  ConstantMachine.evalOperand runtime actual classifyConstantError constant

/-- Legacy explicit-value entry point. It retains rejection of mismatched
documents while sharing the production evaluation implementation. -/
def evalOperand (prepared : CompilerConstantQueries.Prepared) (runtime : RuntimeMetadata)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (base : ConstantMachine.Queries K User)
    (classifyConstantError : ConstantError → StepError)
    (constant : MIR.ConstOperand) : MachineHooks.M K User (OpTy Provenance) :=
  evalOperandBound (CompilerConstantQueries.bind prepared runtime) site functions arithmetic
    externStatic base classifyConstantError constant
/-- Canonical source path. Its deep compatibility computation was performed
once by `CompilerProviders.prepare`; on a false cached result the same error
still occurs at the original demand point, before frame/site checks. -/
def evalAtBound {prepared : CompilerConstantQueries.Prepared} {runtime : RuntimeMetadata}
    (binding : CompilerConstantQueries.Binding prepared runtime)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyConstantError : ConstantError → StepError)
    (constant : MIR.ConstOperand) (known : Option LocalLayout := none)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool) := none) :
    MachineHooks.M K User (OpTy Provenance) := do
  unless binding.compatible do
    throw (.invalidProgram "constant runtime/compiler evidence document mismatch")
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity.index == site.bodyIndex do
    throw (.invalidProgram "constant operand site belongs to another canonical body")
  unless frame.location == .mir site.location do
    throw (.invalidProgram "constant operand site differs from current MIR location")
  let evidence := (prepared.evidence.filter (·.site == site)).map (·.query)
  let actual := ConstantMachine.fromCompiler functions arithmetic externStatic
    (normalizationFromEvidence evidence) (evaluationFromEvidence evidence)
  ConstantMachine.evalOperandWithLayout runtime actual classifyConstantError constant known checkKnown

/-- Legacy explicit-value entry point. It preserves mismatch rejection for
arbitrary callers while canonical code uses its retained prepared binding. -/
def evalAt (prepared : CompilerConstantQueries.Prepared) (runtime : RuntimeMetadata)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyConstantError : ConstantError → StepError)
    (constant : MIR.ConstOperand) (known : Option LocalLayout := none)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool) := none) :
    MachineHooks.M K User (OpTy Provenance) := do
  evalAtBound (CompilerConstantQueries.bind prepared runtime) site functions arithmetic
    externStatic classifyConstantError constant known checkKnown
end Miri.Input.CompilerConstantMachine
