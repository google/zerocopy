import Miri.Interpreter.OperandPath
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.PlaceMachine

/-! Whole-state operand.rs local/operand evaluation. Immediate locals remain
immediate; dynamic indirect projections use the stateful place projector. -/
namespace Miri.Interpreter.OperandMachine
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (M State)
structure Hooks (K User C : Type) where
  compiler : PlaceMachine.CompilerHooks K User C
  projection : PlaceProjectionHooks Provenance (State K User) C MachineHooks.FrameExtra
  layoutCompatible : LocalLayout → LocalLayout → Except StepError Bool
  checkPlaceType : C → Place → OpTy Provenance → M K User Unit
  dereference : C → OpTy Provenance → M K User (MPlaceTy Provenance)
  runtimeChecks : C → RuntimeChecks → M K User Bool
  boolLayout : C → M K User LocalLayout
  constant : C → ConstOperand → Option LocalLayout → M K User (OpTy Provenance)
  constantAt : C → OperandPath → ConstOperand → Option LocalLayout → M K User (OpTy Provenance) := fun c _ => constant c

private def lift (result : Except StepError A) : M K User A :=
  match result with | .ok value => pure value | .error error => throw error
private def stack (result : Except StackError A) : M K User A := lift (result.mapError StepError.stack)
private def projection (result : Except ProjectionError A) : M K User A :=
  lift (result.mapError fun error => match error with
    | .machineError error => error
    | .bounds length index => .undefinedBehavior s!"index out of bounds: {index} >= {length}"
    | .pointerArithOverflow => .undefinedBehavior "pointer arithmetic overflow"
    | .scalar e => ScalarOps.scalarError e
    | .immediate e => ScalarOps.immediateError e
    | .obligation message => .unsupported message
    | other => .invalidProgram s!"operand projection: {reprStr other}")

def localToOp (h : Hooks K User C) (c : C) (id : LocalId) (known : Option LocalLayout) : M K User (OpTy Provenance) := do
  let frame ← MachineHooks.currentFrame
  let old ← stack (frame.getLocal id)
  let layout ← match old.layout with
    | some layout => pure layout
    | none =>
      let layout ← match known with
        | none => h.compiler.layout c id
        | some known => do
          if h.compiler.debugAssertions then
            let computed ← h.compiler.layout c id
            unless ← lift (h.layoutCompatible computed known) do
              throw (.invalidProgram "known local layout differs from compiler layout")
          pure known
      let frame ← MachineHooks.currentFrame
      let (updated,layout) ← stack (frame.getOrCacheLocalLayout id layout)
      MachineHooks.setCurrentFrame updated
      pure layout
  let op ← stack ((← MachineHooks.currentFrame).getLocalOperand id)
  if let .immediate _ := op then
    if layout.layout.backendRepr.isUnsized then throw (.invalidProgram "unsized immediate local")
    unless ← h.compiler.validationInProgress do MachineHooks.afterLocalRead id
  return ⟨op,layout⟩

def field (h : Hooks K User C) (c : C) (base : OpTy Provenance) (index : Nat) : M K User (OpTy Provenance) := do
  match base.op with
  | .immediate _ => projection (projectField (← h.compiler.projection c) base index)
  | .indirect memory =>
    let projected ← PlaceDynamic.field h.projection c ⟨.memory memory,base.layout⟩ index
    match projected.ref with
    | .memory memory => return ⟨.indirect memory,projected.layout⟩
    | .local .. => throw (.invalidProgram "indirect field projection became local")

def project (h : Hooks K User C) (c : C) (base : OpTy Provenance) (elem : ProjectionElem) : M K User (OpTy Provenance) := do
  if let .Field index _ := elem then return ← field h c base index
  if elem == .Deref then
    let place ← h.dereference c base
    return ⟨.indirect place.mplace,place.layout⟩
  match base.op with
  | .indirect memory =>
    let next ← PlaceDynamic.project h.projection c ⟨.memory memory,base.layout⟩ elem
    match next.ref with
    | .memory memory => return ⟨.indirect memory,next.layout⟩
    | .local .. => throw (.invalidProgram "indirect projection became local")
  | .immediate _ =>
    let cx ← h.compiler.projection c
    match elem with
    | .Subslice fromIndex to fromEnd =>
      if fromIndex >= 2^64 || to >= 2^64 then throw (.invalidProgram "MIR subslice exceeds u64")
      let (offset,count) ← projection (prepareSubslice cx base (UInt64.ofNat fromIndex) (UInt64.ofNat to) fromEnd)
      let (layout,metadata) ← h.projection.subsliceLayout c base.layout count
      projection (base.offsetWithMeta cx offset .inbounds metadata layout)
    | .Index id =>
      let index ← h.projection.localIndex c id
      projection (projectIndex cx base index)
    | _ => projection (Miri.Interpreter.project cx base elem)

def evalPlaceToOp (h : Hooks K User C) (c : C) (place : Place) (known : Option LocalLayout) : M K User (OpTy Provenance) := do
  let mut op ← localToOp h c place.localId (if place.projection.isEmpty then known else none)
  for elem in place.projection do op ← project h c op elem
  h.checkPlaceType c place op
  return op

/-- Copy and Move share source behavior; no invented move invalidation. -/
def evalOperand (h : Hooks K User C) (c : C) (operand : MIR.Operand) (known : Option LocalLayout) : M K User (OpTy Provenance) := do
  match operand with
  | .Copy place | .Move place => evalPlaceToOp h c place known
  | .Constant value => h.constant c value known
  | .RuntimeChecks checks =>
    let value ← h.runtimeChecks c checks
    let layout ← h.boolLayout c
    return ⟨.immediate (.scalar (.fromBool value)),layout⟩
/-- The path is carried by the structural caller, not recovered from the operand. -/
def evalOperandAt (h : Hooks K User C) (c : C) (path : OperandPath)
    (operand : MIR.Operand) (known : Option LocalLayout) : M K User (OpTy Provenance) :=
  match operand with
  | .Constant value =>
    -- OperandPath identifies the field holding the MIR Operand. Exported
    -- ConstOperand query evidence is keyed at its nested `constant` payload,
    -- so carry the final constructor edge rather than querying the wrapper.
    h.constantAt c (path.push (.field "constant")) value known
  | _ => evalOperand h c operand known
end Miri.Interpreter.OperandMachine
