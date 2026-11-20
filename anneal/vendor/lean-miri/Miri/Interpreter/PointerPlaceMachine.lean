import Miri.Interpreter.IntrinsicMachine

/-! Source place.rs pointer→place construction and deref_pointer, on the
canonical Miri address/alignment/validity state. Construction merely caches
misalignment; only typed safe-pointer dereference checks dereferenceability. -/
namespace Miri.Interpreter.PointerPlaceMachine
open Miri.ABI Miri.Memory Miri.MIR
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U
inductive Kind where
  | reference | box | raw | other
  deriving DecidableEq, Repr
inductive UnsizedTail where
  | dynamic (expectedTrait : Nat)
  | slice | str | foreign | other
  deriving Repr
structure Compiler (K U C : Type) where
  kind : C → TyId → M K U Kind
  builtinDeref : C → TyId → M K U (Option TyId)
  layoutOf : C → TyId → M K U LocalLayout
  structTail : C → TyId → M K U UnsizedTail

private def liftResult (result : Except StepError A) : MachineHooks.M K User A :=
  match result with | .ok value => pure value | .error error => throw error

/-- Representation access to the actual alignment policy and shared pointer
promises. These are data projections, not an operation-result oracle. -/
structure AlignmentContext (User : Type) where
  policy : User → ValidityMachine.AlignmentCheck
  promises : User → Array (AllocId × Size × Align)

def controlledAlignment : AlignmentContext (ValidityMachine.UserState U) :=
  ⟨(·.payload.alignment),(·.symbolicAlignment)⟩

/-- Source is_ptr_misaligned, including the no-resolve disabled/one-byte path,
allocation symbolic policy, and integer-address fallback. -/
def misalignmentWith (access : PlaceMachine.AccessConfig K User) (context : AlignmentContext User)
    (ptr : Pointer (Option Provenance)) (required : Align) : MachineHooks.M K User (Option Misalignment) := do
  let state ← get
  let policy := context.policy state.machine.user
  if policy == .None || required.pow2 == 0 then return none
  let resolution := access.resolvePointer state.machine.memory ptr 0 state.machine
  let resolved ← match resolution with
    | .error error machine => set {state with machine}; throw error
    | .ok value machine => set {state with machine}; pure value
  let state ← get
  let mut override := none
  if let .ok resolved := resolved then
    let info ← liftResult (state.machine.memory.getAllocInfo resolved.allocId |>.mapError
      fun error => .invalidProgram s!"pointer place allocation metadata: {reprStr error}")
    let promise := ((context.promises state.machine.user).find? (fun entry => entry.1 == resolved.allocId)).map
      (fun entry => (entry.2.1,entry.2.2))
    override ← liftResult (PointerMachine.symbolicAlignment (policy == .Symbolic)
      info.kind info.align promise resolved.offset required |>.mapError
      fun error => .invalidProgram s!"pointer place symbolic alignment: {reprStr error}")
  liftResult (isPtrMisaligned ptr required true (fun _ _ => resolved) state.machine.memory.getAllocInfo
    (fun _ _ _ _ _ => override) |>.mapError fun error => .invalidProgram s!"pointer place alignment: {reprStr error}")

/-- Existing concrete control/pointer-state API uses the same generic rule. -/
def misalignment (access : ValidityMachine.Access K U)
    (ptr : Pointer (Option Provenance)) (required : Align) : M K U (Option Misalignment) :=
  misalignmentWith access controlledAlignment ptr required


def withMetadata (access : ValidityMachine.Access K U) (ptr : Pointer (Option Provenance))
    (metadata : MemPlaceMeta Provenance) (layout : LocalLayout) (unaligned : Bool) : M K U (MPlaceTy Provenance) := do
  let mismatch ← if unaligned then pure none else misalignment access ptr layout.layout.align.abi
  pure ⟨⟨ptr,metadata,mismatch⟩,layout⟩

def fromPointer (access : ValidityMachine.Access K U) (ptr : Pointer (Option Provenance))
    (layout : LocalLayout) (unaligned : Bool) : M K U (MPlaceTy Provenance) := do
  unless layout.layout.isSized do throw (.invalidProgram "ptr_to_mplace requires sized layout")
  withMetadata access ptr .none layout unaligned

/-- Source builtin_deref/layout query precedes scalar/metadata extraction.
No dynamic-layout or pointer validity check occurs in this constructor. -/
def fromImmediate (access : ValidityMachine.Access K U) (compiler : Compiler K U C)
    (choice : C) (value : RvalueImmTy Provenance) : M K U (MPlaceTy Provenance) := do
  let some ty ← compiler.builtinDeref choice value.layout.ty
    | throw (.invalidProgram "imm_ptr_to_mplace called on non-pointer type")
  let layout ← compiler.layoutOf choice ty
  let (scalar,metadata) ← liftResult (value.imm.toScalarAndMeta |>.mapError ScalarOps.immediateError)
  let ptr ← liftResult (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  withMetadata access ptr metadata layout false

/-- Full source typed dereference: kind check, read, place construction,
conditional validity, safe-pointer null/layout/access/alignment; raw-pointer
unsized dynamic tails validate only their vtable identity/type. -/
def dereference [DecidableEq K] (access : ValidityMachine.Access K U) (compiler : Compiler K U C)
    (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (vtable : VTableHooks Provenance (State K U) C F A) (fuel : Nat)
    (choice : C) (source : OpTy Provenance) : M K U (MPlaceTy Provenance) := do
  let kind ← compiler.kind choice source.layout.ty
  if kind == .other then throw (.invalidProgram "dereferencing non-pointer type")
  let value ← PlaceMachine.readImmediate access source
  let place ← fromImmediate access compiler choice value
  unless ← ValidityMachine.enforceValidity do return place
  if kind == .reference || kind == .box then
    let name := if kind == .reference then "reference" else "box"
    let scalar ← liftResult (Scalar.fromMaybePointer access.runtime.base place.mplace.ptr |>.mapError ScalarOps.scalarError)
    if ← ValidityMachine.scalarMayBeNull scalar then throw (.undefinedBehavior s!"dereferencing a null {name}")
    let sizeAlign ← DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel place.mplace.metadata place.layout
    let (size,align) := sizeAlign.getD (place.layout.layout.size,place.layout.layout.align.abi)
    ValidityMachine.checkPointerAccess access place.mplace.ptr size
    ValidityMachine.checkPointerAlign access place.mplace.ptr align
  else
    unless kind == .raw do throw (.invalidProgram "dereferencing unexpected pointer kind")
    if !place.layout.layout.isSized then
      match ← compiler.structTail choice place.layout.ty with
      | .dynamic expected =>
        let .metadata metadata := place.mplace.metadata | throw (.invalidProgram "dynamic raw pointer missing metadata")
        let ptr ← liftResult (metadata.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
        let _ ← VTable.getPtrVTableType vtable choice ptr (some expected)
        pure ()
      | .slice | .str | .foreign => pure ()
      | .other => throw (.invalidProgram "unexpected unsized raw-pointer tail")
  pure place

/-- Close ordinary and simple-deref PlaceHooks with the same source driver.
Simple deref skips kind/validity checks and performs only read+construction. -/
def bindCompiler [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : Compiler K U C) (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (vtable : VTableHooks Provenance (State K U) C F A) (fuel : Nat)
    (base : PlaceMachine.CompilerHooks K (ValidityMachine.UserState U) C) :
    PlaceMachine.CompilerHooks K (ValidityMachine.UserState U) C :=
  let places := PlaceMachine.placeHooks access allocation base
  {base with deref := fun c source skip => do
    let operand ← placeToOp places c source
    let memory ← if skip then do
        fromImmediate access compiler c (← PlaceMachine.readImmediate access operand)
      else dereference access compiler dynamic vtable fuel c operand
    pure ⟨.memory memory.mplace,memory.layout⟩ }
/-- Unary PtrMetadata's source validity event executes before extracting the
metadata scalar. Immediates remain typed and do not gain spurious memory reads. -/
def bindScalarOps [DecidableEq K] (access : ValidityMachine.Access K U)
    (compiler : Compiler K U C) (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (vtable : VTableHooks Provenance (State K U) C F A) (fuel : Nat)
    (base : ScalarOpsHooks Provenance (State K U) C) : ScalarOpsHooks Provenance (State K U) C :=
  {base with derefValidity := fun c value => do
    let _ ← dereference access compiler dynamic vtable fuel c ⟨.immediate value.imm,value.layout⟩
    pure ()}

def bindCast [DecidableEq K] (access : ValidityMachine.Access K U)
    (compiler : Compiler K U C) (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (vtable : VTableHooks Provenance (State K U) C F A) (fuel : Nat)
    (base : CastHooks Provenance (State K U) C V) : CastHooks Provenance (State K U) C V :=
  {base with derefPointer := fun c source => do
    let _ ← dereference access compiler dynamic vtable fuel c source
    pure ()}

/-- Close the common pointer-conversion/dereference leaves of core intrinsics
and atomic access, reusing precisely the same validity driver as ordinary MIR. -/
def bindIntrinsics [DecidableEq K] (access : ValidityMachine.Access K U)
    (compiler : Compiler K U C) (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (vtable : VTableHooks Provenance (State K U) C F A) (fuel : Nat)
    (base : IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance)) :
    IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let deref := fun c source => do
    let memory ← dereference access compiler dynamic vtable fuel c source
    pure (RuntimePlace.mk (.memory memory.mplace) memory.layout)
  let scalar := bindScalarOps access compiler dynamic vtable fuel base.scalarOps
  {base with
    scalarOps := scalar
    derefPointer := deref
    immPointerToPlace := fun c value => do
      let memory ← fromImmediate access compiler c value
      pure ⟨.indirect memory.mplace,memory.layout⟩
    atomicHooks := {base.atomicHooks with derefPointer := deref, scalarOps := scalar}
    simdHooks := {base.simdHooks with
      scalarOps := scalar
      castHooks := bindCast access compiler dynamic vtable fuel base.simdHooks.castHooks
      derefImmediate := fun c value => do
        let memory ← fromImmediate access compiler c value
        pure ⟨.memory memory.mplace,memory.layout⟩}}

end Miri.Interpreter.PointerPlaceMachine
