import Miri.Interpreter.Constant
import Miri.Interpreter.FunctionPointers

/-! Canonical constant-operand machine binding. Compiler CTFE pointer IDs
remain allocation IDs until actual root-tag/address adjustment; they are never
used directly as absolute guest addresses. -/
namespace Miri.Interpreter.ConstantMachine
open Miri.ABI Miri.Memory Miri.MIR
open Miri.TreeBorrows (BorrowTree)
structure Context (K User : Type) where
  state : MachineHooks.State K User
  pendingError : Option StepError
abbrev Queries K User := ConstantQueries Provenance BorrowTree K (Context K User)

private def machineAction (action : MachineHooks.M K User A) :
    ConstantM Provenance BorrowTree K (Context K User) A := fun constant =>
  let initial := {constant.hooks.state with machine := {constant.hooks.state.machine with memory := constant.memory}}
  match action initial with
  | .ok value result => .ok value {constant with memory := result.machine.memory, hooks := ⟨result,constant.hooks.pendingError⟩}
  | .error error result => .error (.query "constant machine operation failed")
      {constant with memory := result.machine.memory, hooks := ⟨result,some error⟩}

/-- Source M::adjust_alloc_root_pointer with the original CTFE offset. -/
private def adjustedPointer (functions : FunctionPointers.Hooks K User Other)
    (arithmetic : PointerArithmetic) (pointer : Pointer CtfeProvenance) :
    ConstantM Provenance BorrowTree K (Context K User) (Pointer Provenance) := machineAction do
  let root ← FunctionPointers.rootPointer functions pointer.provenance.allocId
  match root.wrappingOffset pointer.offset arithmetic with
  | .ok pointer => pure pointer
  | .error error => throw (.invalidProgram s!"constant root pointer offset: {reprStr error}")

/-- Source constantGlobalRootPointer performs TLS/extern classification first.
Miri ignores the CTFE immutable flag; the original offset is retained after
actual root provenance and absolute base-address assignment. -/
def queries (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K User (Pointer Provenance))
    (compiler : Queries K User) : Queries K User :=
  {compiler with
    adjustGlobalRootPointer := adjustedPointer functions arithmetic
    externStaticPointer := fun definition => machineAction (externStatic definition)}

/-- Construct the whole dictionary from actual compiler evidence and machine
operations. No unbound placeholder dictionary is required by production. -/
def fromCompiler (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K User (Pointer Provenance))
    (normalize : CallInstance → MirConst → Except ConstantError MirConst)
    (evaluate : CallInstance → MirConst → SpanRef → Except ConstantError ConstValue) : Queries K User :=
  {instantiateAndNormalize := fun fnInstance constant =>
      match normalize fnInstance constant with
      | .ok value => pure value
      | .error error => throw error
   evaluate := fun fnInstance constant span =>
      match evaluate fnInstance constant span with
      | .ok value => pure value
      | .error error => throw error
   adjustGlobalRootPointer := adjustedPointer functions arithmetic
   externStaticPointer := fun definition => machineAction (externStatic definition)}

/-- Lift the existing source interpreter without losing post-error machine
updates. Error categories from actual machine operations are preserved exactly;
compiler/constant subsystem errors use the required source classifier. -/
def evalOperandWithLayout (runtime : Input.RuntimeMetadata) (compiler : Queries K User)
    (classifyConstantError : ConstantError → StepError)
    (constant : ConstOperand) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool)) :
    MachineHooks.M K User (OpTy Provenance) := fun initial =>
  match initial.stack.currentFrame? with
  | none => .error (.stack .emptyStack) initial
  | some frame =>
    let source : ConstantState Provenance BorrowTree K (Context K User) :=
      ⟨initial.machine.memory,⟨initial,none⟩,frame.functionInstance⟩
    match evalConstOperandWithLayout runtime compiler constant known
        (checkKnown.map fun check left right => machineAction (check left right)) source with
    | .ok value result => .ok value {result.hooks.state with machine :=
        {result.hooks.state.machine with memory := result.memory}}
    | .error error result => .error (result.hooks.pendingError.getD (classifyConstantError error))
        {result.hooks.state with machine := {result.hooks.state.machine with memory := result.memory}}
def evalOperand (runtime : Input.RuntimeMetadata) (compiler : Queries K User)
    (classifyConstantError : ConstantError → StepError) (constant : ConstOperand) :
    MachineHooks.M K User (OpTy Provenance) :=
  evalOperandWithLayout runtime compiler classifyConstantError constant none none

/-- Direct compiler ConstValue conversion. No synthetic MIR operand, source
span, normalization callback or evaluation callback is introduced. Machine
effects preceding conversion failure are retained exactly as in operand eval. -/
def evalValueWithLayout (runtime : Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyConstantError : ConstantError → StepError)
    (value : ConstValue) (ty : TyId) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool)) :
    MachineHooks.M K User (OpTy Provenance) := fun initial =>
  match initial.stack.currentFrame? with
  | none => .error (.stack .emptyStack) initial
  | some frame =>
    let compiler : ConstantValueQueries Provenance BorrowTree K (Context K User) :=
      ⟨adjustedPointer functions arithmetic, fun definition => machineAction (externStatic definition)⟩
    let source : ConstantState Provenance BorrowTree K (Context K User) :=
      ⟨initial.machine.memory,⟨initial,none⟩,frame.functionInstance⟩
    match valueToOpWithLayout runtime compiler value ty known
        (checkKnown.map fun check left right => machineAction (check left right)) source with
    | .ok value result => .ok value {result.hooks.state with machine :=
        {result.hooks.state.machine with memory := result.memory}}
    | .error error result => .error (result.hooks.pendingError.getD (classifyConstantError error))
        {result.hooks.state with machine := {result.hooks.state.machine with memory := result.memory}}
end Miri.Interpreter.ConstantMachine
