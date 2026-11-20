import Miri.Interpreter.OperandPath
import Miri.Interpreter.Projection
import Miri.Interpreter.Step
import Miri.TreeBorrows.RetagPolicy

/-! Pinned `interpret/step.rs:160-300` dispatcher. Required machine operations
are effectful obligations; every failure preserves its resulting state. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory
open Miri.TreeBorrows.RetagPolicy

structure RvalueImmTy (Prov : Type) where
  imm : Immediate Prov
  layout : TyAndLayout MIR.TyId
  deriving DecidableEq, Repr

abbrev RvalueM (S A : Type) := EStateM StepError S A

structure RvalueHooks (Prov S C V : Type) where
  placeLayout : V → TyAndLayout MIR.TyId
  evalPlace : C → MIR.Place → Bool → RvalueM S V
  evalOperand : C → MIR.Operand → Option (TyAndLayout MIR.TyId) → RvalueM S (OpTy Prov)
  evalOperandAt : C → OperandPath → MIR.Operand → Option (TyAndLayout MIR.TyId) → RvalueM S (OpTy Prov) := fun c _ => evalOperand c
  evalPlaceToOp : C → MIR.Place → Option (TyAndLayout MIR.TyId) → RvalueM S (OpTy Prov)
  readImmediate : C → OpTy Prov → RvalueM S (RvalueImmTy Prov)
  writeImmediate : C → Immediate Prov → V → RvalueM S Unit
  writePointer : C → Pointer (Option Prov) → V → RvalueM S Unit
  threadLocalPointer : C → MIR.DefId → RvalueM S (Pointer (Option Prov))
  withRetagMode : {A : Type} → C → RetagMode → RvalueM S A → RvalueM S A
  copyOp : C → OpTy Prov → V → RvalueM S Unit
  copyOpAllowTransmute : C → OpTy Prov → V → RvalueM S Unit
  binaryOp : C → MIR.BinOp → RvalueImmTy Prov → RvalueImmTy Prov → RvalueM S (RvalueImmTy Prov)
  unaryOp : C → MIR.UnOp → RvalueImmTy Prov → RvalueM S (RvalueImmTy Prov)
  writeAggregate : C → MIR.AggregateKind → Array MIR.Operand → V → RvalueM S Unit
  writeRepeat : C → MIR.Operand → V → RvalueM S Unit
  forceAllocation : C → V → RvalueM S (MemPlace Prov)
  toRef : C → MemPlace Prov → RvalueM S (Immediate Prov)
  enforceValidity : C → TyAndLayout MIR.TyId → RvalueM S Bool
  retagPtrValue : C → RvalueImmTy Prov → MIR.TyId → RvalueM S (Option (RvalueImmTy Prov))
  placeBaseRaw : C → MIR.Place → RvalueM S Bool
  normalize : C → MIR.TyId → RvalueM S MIR.TyId
  cast : C → OpTy Prov → MIR.CastKind → MIR.TyId → V → RvalueM S Unit
  readDiscriminant : C → OpTy Prov → RvalueM S MIR.VariantIndex
  discriminantForVariant : C → MIR.TyId → MIR.VariantIndex → RvalueM S (RvalueImmTy Prov)

private def assertRvalueLayout (actual expected : TyAndLayout MIR.TyId) : RvalueM S Unit :=
  if actual == expected then pure () else throw (.invalidProgram "rvalue result layout mismatch")

/-- Destination evaluation is always first, with the source's skip-validity flag.
No hook has a default implementation or a default successful outcome. -/
def evalRvalueIntoPlace (h : RvalueHooks P S C V) (choice : C)
    (rvalue : MIR.Rvalue) (place : MIR.Place) : RvalueM S Unit := do
  let dest ← h.evalPlace choice place true
  let layout := h.placeLayout dest
  match rvalue with
  | .ThreadLocalRef definition =>
      let ptr ← h.threadLocalPointer choice definition
      h.writePointer choice ptr dest
  | .Use operand retag =>
      let op ← h.evalOperandAt choice (OperandPath.rvalue "operand") operand (some layout)
      h.withRetagMode choice (if retag == .Yes then .Default else .None)
        (h.copyOp choice op dest)
  | .CopyForDeref _ => throw (.invalidProgram "CopyForDeref in runtime MIR")
  | .BinaryOp operator left right =>
      let left ← h.evalOperandAt choice (OperandPath.rvalue "left") left (if operator.leftHomogeneous then some layout else none)
      let left ← h.readImmediate choice left
      let right ← h.evalOperandAt choice (OperandPath.rvalue "right") right (if operator.rightHomogeneous then some left.layout else none)
      let right ← h.readImmediate choice right
      let result ← h.binaryOp choice operator left right
      assertRvalueLayout result.layout layout
      h.writeImmediate choice result.imm dest
  | .UnaryOp operator operand =>
      let val ← h.evalOperandAt choice (OperandPath.rvalue "operand") operand (if operator.homogeneous then some layout else none)
      let val ← h.readImmediate choice val
      let result ← h.unaryOp choice operator val
      assertRvalueLayout result.layout layout
      h.writeImmediate choice result.imm dest
  | .Aggregate kind operands => h.writeAggregate choice kind operands dest
  | .Repeat operand _ => h.writeRepeat choice operand dest
  | .Ref _ borrow src =>
      let src ← h.evalPlace choice src true
      let src ← h.forceAllocation choice src
      let imm ← h.toRef choice src
      let val : RvalueImmTy P := ⟨imm, layout⟩
      let mode := if borrow == .Mut .TwoPhaseBorrow then RetagMode.TwoPhase else .Default
      h.withRetagMode choice mode do
        let mut val := val
        if !(← h.enforceValidity choice val.layout) then
          if let some newVal ← h.retagPtrValue choice val val.layout.ty then val := newVal
        h.writeImmediate choice val.imm dest
  | .Reborrow _ mutability src =>
      let op ← h.evalPlaceToOp choice src none
      if mutability == .Not then h.copyOpAllowTransmute choice op dest
      else h.copyOp choice op dest
  | .RawPtr kind src =>
      let baseRaw ← h.placeBaseRaw choice src
      let src ← h.evalPlace choice src false
      let src ← h.forceAllocation choice src
      let imm ← h.toRef choice src
      let mut val : RvalueImmTy P := ⟨imm, layout⟩
      if !baseRaw && kind != .FakeForPtrMetadata then
        val ← h.withRetagMode choice .Raw do
          return (← h.retagPtrValue choice val val.layout.ty).getD val
      h.writeImmediate choice val.imm dest
  | .Cast kind operand ty =>
      let src ← h.evalOperandAt choice (OperandPath.rvalue "operand") operand none
      let ty ← h.normalize choice ty
      h.cast choice src kind ty dest
  | .Discriminant src =>
      let op ← h.evalPlaceToOp choice src none
      let variant ← h.readDiscriminant choice op
      let discr ← h.discriminantForVariant choice op.layout.ty variant
      h.writeImmediate choice discr.imm dest
  | .WrapUnsafeBinder operand _ =>
      let op ← h.evalOperandAt choice (OperandPath.rvalue "operand") operand none
      h.copyOpAllowTransmute choice op dest

/-- Adapt the effect result to the statement driver's state-preserving result. -/
def runRvalue (action : RvalueM S A) (state : S) : StepResult S A :=
  match action state with
  | .ok value state => (state, .ok value)
  | .error error state => (state, .error error)

end Miri.Interpreter
