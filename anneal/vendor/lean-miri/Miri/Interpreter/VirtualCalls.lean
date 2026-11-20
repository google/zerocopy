import Miri.Interpreter.VTable
import Miri.Interpreter.FunctionCalls
import Miri.Interpreter.PlaceMachine
import Miri.ABI.FnAbi

/-! Stateful virtual receiver/vtable dispatch, dynamic drop and caller-location
selection from pinned interpret/call.rs and eval_context.rs. Complete compiler
instances, argument rebasing, type constructors and inline-scope span queries
remain required compiler leaves; no ABI or function identity is guessed. -/
namespace Miri.Interpreter.VirtualCalls
open Miri.ABI Miri.Memory Miri.MIR

inductive ReceiverKind where
  | reference | rawPointer | dynamic | other
  deriving DecidableEq, Repr

structure DynamicData where
  predicates : Nat
  principal : Option Nat

/-- SourceScopeData fields consumed by Body::caller_location_span. -/
structure CallerScope where
  inlined : Option (CallInstance × SpanRef)
  inlinedParentScope : Option Nat

structure CompilerHooks (S C : Type) where
  classifyReceiver : TyId → CallM S ReceiverKind
  fieldLayout : LocalLayout → Nat → CallM S LocalLayout
  structTailForCodegen : TyId → CallM S TyId
  dynamicData : TyId → CallM S (Option DynamicData)
  mutPointerType : TyId → CallM S TyId
  mutReferenceType : TyId → CallM S TyId
  builtinDeref : TyId → CallM S (Option TyId)
  layoutOf : TyId → CallM S LocalLayout
  parentTrait : DefId → CallM S DefId
  /-- from_assoc→erase_self_ty→with_self_ty→args.rebase_onto, all using
  compiler generic arguments, not an assumed first-argument replacement. -/
  rebaseVirtualArgs : Array GenericArg → DefId → TyId → CallM S (Array GenericArg)
  expectResolveForVTable : C → DefId → Array GenericArg → CallM S CallInstance
  resolveDropGlue : TyId → CallM S CallInstance
  requiresCallerLocation : CallInstance → CallM S Bool
  sourceScope : BodyIdentity → CallInstance → Body → Nat → CallM S CallerScope
  unitLayout : CallM S LocalLayout

structure Hooks (P S C E : Type) where
  debugAssertions : Bool
  compiler : CompilerHooks S C
  target : TargetDataLayout
  vtable : VTableHooks P S C CallInstance (FnAbi TyId)
  getFrame : CallM S (Frame P LocalLayout E)
  readImmediate : C → OpTy P → CallM S (RvalueImmTy P)
  immPtrToMPlace : C → RvalueImmTy P → CallM S (MPlaceTy P)
  projectField : C → OpTy P → Nat → CallM S (OpTy P)

private def invalid (message : String) : CallM S A := throw (.invalidProgram message)
private def scalarError (value : Except ImmediateError A) : CallM S A :=
  match value with | .ok value => pure value | .error error => invalid (reprStr error)

/-- place.rs imm_ptr_to_mplace: type/deref/layout queries precede scalar
extraction; this caches misalignment without checking pointer dereferenceability
or dynamic size. An unaligned raw receiver can still resolve a virtual method. -/
def pointerPlace [PointerProvenance P] (compiler : CompilerHooks S C)
    (target : TargetDataLayout)
    (misaligned : Pointer (Option P) → Align → CallM S (Option Misalignment))
    (value : RvalueImmTy P) : CallM S (MPlaceTy P) := do
  let some pointee ← compiler.builtinDeref value.layout.ty
    | invalid "imm_ptr_to_mplace called on non-pointer type"
  let layout ← compiler.layoutOf pointee
  let (scalar, metadata) ← scalarError value.imm.toScalarAndMeta
  let pointer ← match scalar.toPointer target with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let alignment ← misaligned pointer layout.layout.align.abi
  return ⟨⟨pointer,metadata,alignment⟩,layout⟩

/-- Actual canonical memory reads and existing operand field projection.
Compiler/global-vtable/host-alignment leaves remain explicit dictionaries. -/
def machineHooks [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (projection : PlaceMachine.CompilerHooks K User C)
    (compiler : CompilerHooks (MachineHooks.State K User) C)
    (vtable : VTableHooks Provenance (MachineHooks.State K User) C CallInstance (FnAbi TyId))
    (misaligned : Pointer (Option Provenance) → Align → MachineHooks.M K User (Option Misalignment)) :
    Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra := {
  debugAssertions := projection.debugAssertions
  compiler, target := access.runtime.base, vtable
  getFrame := MachineHooks.currentFrame
  readImmediate := fun _ => PlaceMachine.readImmediate access
  immPtrToMPlace := fun _ => pointerPlace compiler access.runtime.base misaligned
  projectField := fun c receiver index => do
    match Miri.Interpreter.projectField (← projection.projection c) receiver index with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"virtual receiver field: {reprStr error}") }

/-- Source TyAndLayout::non_1zst_field exits immediately on a second non-1-ZST
field; no later field query is executed. It does not project/read field values. -/
def nonOneZstField (compiler : CompilerHooks S C) (layout : LocalLayout) :
    CallM S (Option Nat) := do
  let mut found := none
  for index in [:layout.layout.fields.count] do
    let field ← compiler.fieldLayout layout index
    if !field.layout.is1zst then
      if found.isSome then return none
      found := some index
  return found

/-- Receiver unwrapping performs ordinary typed immediate reads but never a
reference dereference/validity check: raw dyn receivers need not be accessible.
The budget is a concrete runner recursion limit, not source semantics. -/
def receiverPlace (h : Hooks P S C E) (choice : C) : Nat → OpTy P → CallM S (MPlaceTy P)
  | 0, _ => throw (.resourceExhaustion "virtual receiver newtype traversal")
  | budget + 1, receiver => do
    match ← h.compiler.classifyReceiver receiver.layout.ty with
    | .reference | .rawPointer => h.immPtrToMPlace choice (← h.readImmediate choice receiver)
    | .dynamic =>
      let .indirect place := receiver.op | invalid "dynamic receiver must be indirect"
      return ⟨place, receiver.layout⟩
    | .other =>
      let some index ← nonOneZstField h.compiler receiver.layout
        | invalid "DispatchFromDyn receiver does not have exactly one non-1-ZST field"
      receiverPlace h choice budget (← h.projectField choice receiver index)

/-- Exact full-instance consistency assertion after symbolic Method selection.
Compiler rebasing preserves all method-level generic arguments and shim kind. -/
def assertConcrete (compiler : CompilerHooks S C) (choice : C) (dynTy : TyId)
    (definition : DefId) (virtualInstance concreteInstance : CallInstance) : CallM S Unit := do
  let traitDef ← compiler.parentTrait definition
  let args ← compiler.rebaseVirtualArgs virtualInstance.args traitDef dynTy
  let expected ← compiler.expectResolveForVTable choice definition args
  if concreteInstance != expected then invalid "virtual/concrete compiler instance mismatch"

/-- Source Virtual arm: unwrap receiver, inspect dyn tail, check symbolic
vtable, select Method, assert full instance, build thin raw receiver, then patch
only the first caller-ABI argument's type. The real callee ABI check occurs in
the normal recursive Call pipeline, not eagerly at vtable selection. -/
def resolveVirtual [PointerProvenance P] (h : Hooks P S C E) (choice : C) (budget : Nat)
    (virtualInstance : CallInstance) (definition : DefId) (slot : Nat)
    (callerAbi : FnAbi TyId) (args : Array (FnArg P)) :
    CallM S (CallInstance × FnAbi TyId × Array (FnArg P)) := do
  let some first := args[0]? | invalid "virtual call missing receiver"
  let place ← receiverPlace h choice budget first.copyFnArg
  let tail ← h.compiler.structTailForCodegen place.layout.ty
  let some data ← h.compiler.dynamicData tail | invalid "dynamic call on non-dyn tail"
  if place.layout.layout.isSized then invalid "virtual receiver place is sized"
  let metadata ← scalarError place.mplace.metadata.unwrapMeta
  let vptr ← match metadata.toPointer h.target with
    | .ok pointer => pure pointer
    | .error error => throw (ScalarOps.scalarError error)
  let dynTy ← VTable.getPtrVTableType h.vtable choice vptr (some data.predicates)
  let entries ← h.vtable.entries choice data.principal dynTy
  let some (.method concreteInstance) := entries[slot]?
    | throw (.undefinedBehavior "dyn call trying to call something that is not a method")
  assertConcrete h.compiler choice dynTy definition virtualInstance concreteInstance
  let receiverTy ← h.compiler.mutPointerType dynTy
  let scalar ← match Scalar.fromMaybePointer h.target place.mplace.ptr with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let receiverLayout ← h.compiler.layoutOf receiverTy
  let receiver : FnArg P := .Copy ⟨.immediate (.scalar scalar), receiverLayout⟩
  let args ← if bound : 0 < args.size then pure (args.set 0 receiver bound)
    else invalid "virtual receiver disappeared"
  let some firstAbi := callerAbi.args[0]? | invalid "virtual call ABI missing receiver"
  let firstAbi := { firstAbi with layout := { firstAbi.layout with ty := receiverTy } }
  let abiArgs ← if bound : 0 < callerAbi.args.size then pure (callerAbi.args.set 0 firstAbi bound)
    else invalid "virtual ABI receiver disappeared"
  let callerAbi := { callerAbi with args := abiArgs }
  return (concreteInstance, callerAbi, args)

/-- rustc_middle Body::caller_location_span walks only inlined-parent scopes,
stopping inside the first non-track_caller callee; the incoming argument is a
fallback only after the whole inlined chain has been considered. -/
def callerLocationSpan (compiler : CompilerHooks S C) (bodyIdentity : BodyIdentity) (fnInstance : CallInstance)
    (body : Body) (trackedCaller : Option SpanRef) : Nat → SourceInfo → CallM S SpanRef
  | 0, _ => throw (.resourceExhaustion "inlined caller-location scope traversal")
  | budget + 1, sourceInfo => do
    let scope ← compiler.sourceScope bodyIdentity fnInstance body sourceInfo.scope
    let mut sourceInfo := sourceInfo
    if let some (callee,callsite) := scope.inlined then
      if !(← compiler.requiresCallerLocation callee) then return sourceInfo.span
      sourceInfo := { sourceInfo with span := callsite }
    match scope.inlinedParentScope with
    | some parent => callerLocationSpan compiler bodyIdentity fnInstance body trackedCaller budget { sourceInfo with scope := parent }
    | none => return trackedCaller.getD sourceInfo.span

/-- eval_context.rs caller_location: Call's fn_span replaces only SourceInfo's
span; inline-scope-aware compiler handling still receives trackCallerArg. -/
def callerLocation (h : Hooks P S C E) (budget : Nat) : CallM S SpanRef := do
  let frame ← h.getFrame
  let .mir location := frame.location | invalid "caller_location during unwinding"
  let some block := frame.body.basicBlocks[location.block]? | invalid "caller_location block missing"
  let sourceInfo ← if location.statementIndex == block.statements.size then
      let sourceInfo := block.terminator.sourceInfo
      match block.terminator.kind with
      | .Call _ _ _ _ _ _ functionSpan => pure { sourceInfo with span := functionSpan }
      | _ => pure sourceInfo
    else
      match block.statements[location.statementIndex]? with
      | some statement => pure statement.sourceInfo
      | none => invalid "caller_location statement missing"
  callerLocationSpan h.compiler frame.bodyIdentity frame.functionInstance frame.body frame.trackCallerArg budget sourceInfo

/-- Concrete dyn drop unpacks the symbolic vtable's type/layout with a wrapping
zero offset and clears metadata, retaining the canonical pointer/misalignment. -/
def unpackDynForDrop [PointerProvenance P] (h : Hooks P S C E) (choice : C)
    (place : MPlaceTy P) : CallM S (MPlaceTy P) := do
  let some data ← h.compiler.dynamicData place.layout.ty | invalid "drop dynamic data missing"
  let unpacked ← VTable.unpackDynTrait h.vtable choice ⟨.indirect place.mplace,place.layout⟩ data.predicates
  let .indirect memory := unpacked.op | invalid "unpacked dyn drop became immediate"
  return ⟨memory,unpacked.layout⟩

/-- call.rs constructs an erased-region mutable reference, then
mplace_to_imm_ptr converts the place before builtin-deref/layout assertions. -/
def mplaceToMutRef [PointerProvenance P] (h : Hooks P S C E) (place : MPlaceTy P) :
    CallM S (OpTy P) := do
  let ty ← h.compiler.mutReferenceType place.layout.ty
  let immediate ← scalarError (place.mplace.toRef h.target)
  let pointee ← h.compiler.builtinDeref ty
  if pointee != some place.layout.ty then invalid "mutable drop reference pointee mismatch"
  let layout ← h.compiler.layoutOf ty
  return ⟨.immediate immediate, layout⟩

/-- Install actual runtime dispatch and location selection while preserving
mandatory normal-call/ABI/body/machine leaves in the base Call dictionary. -/
def bind [PointerProvenance P] (h : Hooks P S C E) (budget : Nat)
    (base : CallHooks P S C E Other Extern (FnAbi TyId) (ArgAbi TyId)) :
    CallHooks P S C E Other Extern (FnAbi TyId) (ArgAbi TyId) :=
  { base with
    debugAssertions := h.debugAssertions
    resolveVirtual := fun c virtualInstance definition index abi args =>
      resolveVirtual h c budget virtualInstance definition index abi args
    callerLocation := callerLocation h budget
    requiresCallerLocation := h.compiler.requiresCallerLocation
    isDynamic := fun ty => return (← h.compiler.classifyReceiver ty) == .dynamic
    unpackDynForDrop := unpackDynForDrop h
    resolveDropGlue := fun _ ty => h.compiler.resolveDropGlue ty
    mplaceToMutRef := fun _ place => mplaceToMutRef h place
    fakeUnitReturn := fun _ => do
      let layout ← h.compiler.unitLayout
      match FunctionCalls.fakeAllocZst layout with
      | .ok place => pure (.memory place)
      | .error error => throw error }

end Miri.Interpreter.VirtualCalls
