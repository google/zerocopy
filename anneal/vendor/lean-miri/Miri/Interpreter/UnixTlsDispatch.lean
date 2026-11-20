import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.ThreadTls

/-! Common Unix foreign_items.rs pthread TLS and pthread_atfork arms.
Only source-matched symbols evaluate signatures or operands. -/
namespace Miri.Interpreter.UnixTlsDispatch
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev M := EStateM StepError
structure Hooks (S D B I : Type) where
  signatures : ShimSignatures.PrimitiveHooks Provenance S
  signature : String → M S (FnAbi TyId)
  keyLayout : M S LocalLayout
  dereference : OpTy Provenance → LocalLayout → M S (MPlaceTy Provenance)
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  getPointerFnInstance : Pointer (Option Provenance) → M S CallInstance
  currentUserRelevantSpan : M S SpanRef
  activeThread : M S ThreadId
  createKey : Option TlsDestructor → Size → M S TlsKey
  deleteKey : TlsKey → M S Unit
  load : TlsKey → ThreadId → M S (Pointer (Option Provenance))
  store : TlsKey → ThreadId → Pointer (Option Provenance) → M S Unit
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  writeNull : MPlaceTy Provenance → M S Unit
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked pthread TLS argument absent")
private def key (h : Hooks S D B I) (operand : OpTy Provenance) : M S TlsKey := do
  match (← h.readScalar operand).toBits operand.layout.layout.size with
  | .ok bits => pure bits
  | .error error => throw (ScalarOps.scalarError error)

def emulate (h : Hooks S D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless #["pthread_key_create","pthread_key_delete","pthread_getspecific",
      "pthread_setspecific","pthread_atfork"].contains name do return none
  let count := if name == "pthread_key_create" || name == "pthread_setspecific" then 2
    else if name == "pthread_atfork" then 3 else 1
  let args ← ShimSignatures.fixedPrimitive h.signatures name (h.signature name) count abi args
  if name == "pthread_key_create" then
    let place ← h.dereference (← arg args 0) (← h.keyLayout)
    let pointer ← h.readPointer (← arg args 1)
    let destructor ← if pointer.offset.bytes != 0 then do
        let fnInstance ← h.getPointerFnInstance pointer
        let span ← h.currentUserRelevantSpan
        pure (some (⟨fnInstance,span⟩ : TlsDestructor))
      else pure none
    let value ← h.createKey destructor place.layout.layout.size
    let value ← match Scalar.fromUInt value place.layout.layout.size with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    h.writeScalar value place
    h.writeNull dest
  else if name == "pthread_key_delete" then
    h.deleteKey (← key h (← arg args 0))
    h.writeNull dest
  else if name == "pthread_getspecific" then
    let key ← key h (← arg args 0)
    let active ← h.activeThread
    h.writePointer (← h.load key active) dest
  else if name == "pthread_setspecific" then
    let key ← key h (← arg args 0)
    let active ← h.activeThread
    let pointer ← h.readPointer (← arg args 1)
    h.store key active pointer
    h.writeNull dest
  else
    -- Source only reads the three pointers: Miri does not support fork.
    let _ ← h.readPointer (← arg args 0)
    let _ ← h.readPointer (← arg args 1)
    let _ ← h.readPointer (← arg args 2)
    h.writeNull dest
  return some .NeedsReturn

def bind (h : Hooks S D B I)
    (base : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :
    ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I :=
  {base with unix := fun name abi args dest => do
    if let some result ← emulate h name abi args dest then return result
    base.unix name abi args dest}
end Miri.Interpreter.UnixTlsDispatch
