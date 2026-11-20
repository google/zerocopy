import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.ValidityVisitor

/-! FnVal-preserving consumers. Source validity.rs and cast.rs discard the
get_ptr_fn result: machine-extra functions must therefore remain valid there. -/
namespace Miri.Interpreter.FunctionPointerConsumers
open Miri.ABI Miri.Memory
open MachineHooks (State)

private def asInstance : FnVal Other → MachineHooks.M K User CallInstance
  | .Instance callee => pure callee
  | .Other _ => throw (.unsupported "'foreign' function pointers are not supported in this context")
private def entry : VTableEntry CallInstance → VTableEntry (FnVal Other)
  | .dropInPlace => .dropInPlace | .size => .size | .align => .align
  | .vacant => .vacant | .traitVPtr trait => .traitVPtr trait
  | .method callee => .method (.Instance callee)

def vtable (h : FunctionPointers.Hooks K User Other)
    (base : VTableHooks Provenance (State K User) C CallInstance ABI) :
    VTableHooks Provenance (State K User) C (FnVal Other) ABI := {
  target := base.target, isDynamic := base.isDynamic, memoryOffset := base.memoryOffset
  resolvePointer := (FunctionPointers.vtableHooks h base).resolvePointer
  globalVTable := base.globalVTable
  globalFunction := fun _ id => FunctionPointers.getFnAlloc h id
  predicates := base.predicates, normalizePredicate := base.normalizePredicate
  layoutOf := base.layoutOf, eraseAndAnonymize := base.eraseAndAnonymize
  ensureMonomorphicType := base.ensureMonomorphicType, ensureMonomorphicDyn := base.ensureMonomorphicDyn
  globalSalt := base.globalSalt, reserveVTable := base.reserveVTable, globalRootPointer := base.globalRootPointer
  entries := fun c principal ty => return (← base.entries c principal ty).map entry
  assertVirtualInstanceMatches := fun c ty definition virtual actual => do
    let virtual ← asInstance virtual
    let actual ← asInstance actual
    base.assertVirtualInstanceMatches c ty definition virtual actual }

def validity (h : FunctionPointers.Hooks K User Other)
    (base : ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra (FnVal Other) ABI Pad) :
    ValidityVisitor.Hooks Provenance (State K User) C MachineHooks.FrameExtra (FnVal Other) ABI Pad :=
  {base with vtable := {base.vtable with
    globalFunction := fun _ => FunctionPointers.getFnAlloc h
    resolvePointer := fun _ pointer => do
      match pointer.intoPointerOrAddr with
      | .error _ => return .error .danglingInteger
      | .ok pointer =>
        match ← h.ptrGetAlloc pointer with
        | none => return .error .danglingInteger
        | some value => return .ok value }}

def cast (h : FunctionPointers.Hooks K User Other)
    (base : CastHooks Provenance (State K User) C D) : CastHooks Provenance (State K User) C D :=
  {FunctionPointers.castHooks h base with checkFunctionPointer := fun _ pointer => do
    let _ ← FunctionPointers.getPtrFn h pointer
    pure ()}
end Miri.Interpreter.FunctionPointerConsumers
