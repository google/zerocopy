import Miri.Interpreter.Call
import Miri.Interpreter.ScalarOps

/-! Runtime symbolic-vtable rules from pinned `interpret/traits.rs` and
`memory.rs`. The selected tree has no `interpret/vtable.rs`. Global allocation
identity, compiler predicates and function ABI checking are required leaves. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

structure VTablePredicate where
  id : Nat
  stableKey : Nat
  autoTrait : Bool
  deriving DecidableEq, Repr

inductive VTablePointerError where
  | danglingInteger
  | other (error : StepError)
  deriving DecidableEq, Repr

inductive VTableEntry (F : Type) where
  | dropInPlace | size | align | vacant
  | method (function : F)
  | traitVPtr (traitRef : Nat)

structure VTableHooks (P S C F ABI : Type) where
  target : TargetDataLayout
  isDynamic : C → MIR.TyId → RvalueM S Bool
  memoryOffset : C → MemPlace P → Size → OffsetMode → MemPlaceMeta P → RvalueM S (MemPlace P)
  resolvePointer : C → Pointer (Option P) → RvalueM S (Except VTablePointerError (AllocId × Size))
  globalVTable : C → AllocId → RvalueM S (Option (MIR.TyId × Nat))
  globalFunction : C → AllocId → RvalueM S (Option F)
  predicates : C → Nat → RvalueM S (Array VTablePredicate)
  normalizePredicate : C → VTablePredicate → RvalueM S Nat
  layoutOf : C → MIR.TyId → RvalueM S (TyAndLayout MIR.TyId)
  eraseAndAnonymize : C → MIR.TyId → Nat → RvalueM S (MIR.TyId × Nat)
  ensureMonomorphicType : C → MIR.TyId → RvalueM S Unit
  ensureMonomorphicDyn : C → Nat → RvalueM S Unit
  globalSalt : C → RvalueM S Nat
  reserveVTable : C → MIR.TyId → Nat → Nat → RvalueM S AllocId
  globalRootPointer : C → AllocId → RvalueM S (Pointer (Option P))
  entries : C → Option Nat → MIR.TyId → RvalueM S (Array (VTableEntry F))
  assertVirtualInstanceMatches : C → MIR.TyId → MIR.DefId → F → F → RvalueM S Unit

/-- Source symbolic reads separated from reservation and virtual calls, so
machine-level dynamic layout needs no placeholder operational dictionary. -/
structure VTableReadHooks (P S C : Type) where
  resolvePointer : C → Pointer (Option P) → RvalueM S (Except VTablePointerError (AllocId × Size))
  globalVTable : C → AllocId → RvalueM S (Option (MIR.TyId × Nat))
  predicates : C → Nat → RvalueM S (Array VTablePredicate)
  normalizePredicate : C → VTablePredicate → RvalueM S Nat
  layoutOf : C → MIR.TyId → RvalueM S (TyAndLayout MIR.TyId)

def VTableHooks.readHooks (h : VTableHooks P S C F A) : VTableReadHooks P S C :=
  ⟨h.resolvePointer,h.globalVTable,h.predicates,h.normalizePredicate,h.layoutOf⟩

namespace VTable
private def ub (message : String) : RvalueM S A := throw (.undefinedBehavior message)
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def insertPredicate (pred : VTablePredicate) : List VTablePredicate → List VTablePredicate
  | [] => [pred]
  | head :: tail => if pred.stableKey <= head.stableKey then pred :: head :: tail
    else head :: insertPredicate pred tail
private def sortPredicates : List VTablePredicate → List VTablePredicate
  | [] => []
  | head :: tail => insertPredicate head (sortPredicates tail)
private def sortedPredicates (predicates : Array VTablePredicate) : List VTablePredicate :=
  (sortPredicates (predicates.toList.filter (!·.autoTrait))).eraseDups

/-- Source ignores auto traits, sorts by compiler stable comparison, removes
identical predicates, then normalizes each paired predicate before equality. -/
def checkForTypeRead (h : VTableReadHooks P S C) (choice : C) (actual expected : Nat) : RvalueM S Unit := do
  let actual ← h.predicates choice actual
  let expected ← h.predicates choice expected
  let actual := sortedPredicates actual
  let expected := sortedPredicates expected
  if actual.length != expected.length then ub "InvalidVTableTrait"
  for (a, b) in actual.zip expected do
    let a ← h.normalizePredicate choice a
    let b ← h.normalizePredicate choice b
    if a != b then ub "InvalidVTableTrait"

def getPtrVTableTypeRead (h : VTableReadHooks P S C) (choice : C)
    (ptr : Pointer (Option P)) (expectedTrait : Option Nat) : RvalueM S MIR.TyId := do
  let resolution ← h.resolvePointer choice ptr
  let (id, offset) ← match resolution with
    | .ok result => pure result
    | .error .danglingInteger => ub "InvalidVTablePointer"
    | .error (.other _) => invalid "unexpected non-dangling error resolving vtable pointer"
  if offset != Size.ZERO then ub "InvalidVTablePointer"
  let some (ty, actualTrait) ← h.globalVTable choice id | ub "InvalidVTablePointer"
  if let some expected := expectedTrait then checkForTypeRead h choice actualTrait expected
  pure ty

/-- The interpreter consults the symbolic VTable allocation's type and layout;
it does not trust or load the raw size/alignment words of arbitrary memory. -/
def getSizeAndAlignRead (h : VTableReadHooks P S C) (choice : C)
    (ptr : Pointer (Option P)) (expectedTrait : Option Nat) : RvalueM S (Size × Align) := do
  let ty ← getPtrVTableTypeRead h choice ptr expectedTrait
  let layout ← h.layoutOf choice ty
  if !layout.layout.isSized then invalid "there are no vtables for unsized types"
  pure (layout.layout.size, layout.layout.align.abi)

def checkForType (h : VTableHooks P S C F A) (choice : C) (actual expected : Nat) : RvalueM S Unit :=
  checkForTypeRead h.readHooks choice actual expected

def getPtrVTableType (h : VTableHooks P S C F A) (choice : C)
    (ptr : Pointer (Option P)) (expectedTrait : Option Nat) : RvalueM S MIR.TyId :=
  getPtrVTableTypeRead h.readHooks choice ptr expectedTrait

def getSizeAndAlign (h : VTableHooks P S C F A) (choice : C)
    (ptr : Pointer (Option P)) (expectedTrait : Option Nat) : RvalueM S (Size × Align) :=
  getSizeAndAlignRead h.readHooks choice ptr expectedTrait

def getPointer (h : VTableHooks P S C F A) (choice : C) (ty : MIR.TyId)
    (dynType : Nat) : RvalueM S (Pointer (Option P)) := do
  let (ty, dynType) ← h.eraseAndAnonymize choice ty dynType
  h.ensureMonomorphicType choice ty
  h.ensureMonomorphicDyn choice dynType
  let salt ← h.globalSalt choice
  let id ← h.reserveVTable choice ty dynType salt
  h.globalRootPointer choice id

/-- This resolves allocation identity only, as memory.rs::get_ptr_fn does.
Calling it requires ABI/type validation at the actual Call pipeline stage. -/
def getPtrFn (h : VTableHooks P S C F A) (choice : C)
    (ptr : Pointer (Option P)) : RvalueM S F := do
  let resolution ← h.resolvePointer choice ptr
  let (id, offset) ← match resolution with
    | .ok result => pure result
    | .error .danglingInteger => ub "DanglingIntPointer"
    | .error (.other error) => throw error
  if offset != Size.ZERO then ub "InvalidFunctionPointer"
  let some function ← h.globalFunction choice id | ub "InvalidFunctionPointer"
  pure function

def getCallableFunction (h : VTableHooks P S C F A)
    (validateABI : C → F → A → RvalueM S Unit) (choice : C)
    (ptr : Pointer (Option P)) (expectedABI : A) : RvalueM S F := do
  let function ← getPtrFn h choice ptr
  validateABI choice function expectedABI
  pure function

/-- Explicit checked utility for virtual method resolution. This extra ABI
validation is caller-selected; production call.rs validates at frame initialization.
Wrong/vacant/header/supertrait entries are UB, never callable functions. -/
def getMethod (h : VTableHooks P S C F A)
    (validateABI : C → F → A → RvalueM S Unit) (choice : C)
    (ptr : Pointer (Option P)) (expectedTrait : Nat) (principal : Option Nat)
    (index : Nat) (definition : MIR.DefId) (virtualInstance : F) (expectedABI : A) : RvalueM S F := do
  let ty ← getPtrVTableType h choice ptr (some expectedTrait)
  let entries ← h.entries choice principal ty
  let some (.method function) := entries[index]? | ub "dyn call trying to call something that is not a method"
  h.assertVirtualInstanceMatches choice ty definition virtualInstance function
  validateABI choice function expectedABI
  pure function

/-- Source unpack_dyn_trait operates only on an indirect dynamic place, then
changes its layout at zero wrapping offset while clearing the metadata. -/
def unpackDynTrait [PointerProvenance P] (h : VTableHooks P S C F A) (choice : C)
    (op : OpTy P) (expectedTrait : Nat) : RvalueM S (OpTy P) := do
  if !(← h.isDynamic choice op.layout.ty) then invalid "unpack_dyn_trait requires dynamic type"
  let .indirect place := op.op | invalid "dynamic place must be indirect"
  let scalar ← match place.metadata.unwrapMeta with
    | .ok value => pure value
    | .error _ => invalid "dynamic place has no metadata"
  let ptr ← match scalar.toPointer h.target with
    | .ok value => pure value
    | .error reason => throw (ScalarOps.scalarError reason)
  let ty ← getPtrVTableType h choice ptr (some expectedTrait)
  let layout ← h.layoutOf choice ty
  let place ← h.memoryOffset choice place Size.ZERO .wrapping .none
  pure ⟨.indirect place, layout⟩

/-- When a consumer actually loads a scalar field, retain the existing typed
memory-read pipeline and all access/provenance hooks. Symbolic size/alignment
lookup above deliberately does not call this helper. -/
def readMemoryScalar [DecidableEq K] [DecidableEq P] [PointerProvenance P]
    (memory : MemoryState P E K) (state : H) (place : MemPlace P)
    (layout : TyAndLayout MIR.TyId) (runtime : RuntimeTargetDataLayout)
    (ghostMode : Bool) (globalKind : Option K)
    (globalHooks : GlobalAllocationHooks P E K H)
    (accessHooks : AllocationAccessHooks P E K H PE)
    (dynamicLayout : DynamicLayoutResolver P E K H) :
    MemoryOperandResult P E K H (Memory.Scalar P) :=
  Miri.Interpreter.readScalar memory state (.indirect place)
    (localMemoryLayout layout) runtime ghostMode globalKind globalHooks accessHooks dynamicLayout

end VTable
end Miri.Interpreter
