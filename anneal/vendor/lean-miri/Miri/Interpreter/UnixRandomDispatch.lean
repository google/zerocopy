import Miri.Interpreter.RandomMemory
import Miri.Interpreter.ShimSignatures

/-! Source unix/foreign_items.rs random wrappers. OS checks precede ABI
construction; arc4random_buf has unit return and performs no destination write. -/
namespace Miri.Interpreter.UnixRandomDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Hooks (S D B I : Type) where
  random : RandomMemory.Hooks S
  /-- These shims depend only on ABI, symbol and operand primitives. Keeping
  the nonrecursive projection here lets the random family be constructed
  before the Unix dispatcher itself exists. -/
  signatures : ShimSignatures.CoreHooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  signature : String → M S (FnAbi TyId)
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readUsize : OpTy Provenance → M S UInt64
  readI32 : OpTy Provenance → M S Int32
  errnoNegOne : String → MPlaceTy Provenance → M S Unit
  writeNull : MPlaceTy Provenance → M S Unit
  writeTargetUsize : UInt64 → MPlaceTy Provenance → M S Unit

/-- Build the random family directly from source primitives. `random` must be
the configured helpers.rs::gen_random effects (including its host fill or
isolated choice tape); errno and target-isize result writes are supplied by
their actual host/compiler bindings. No whole Unix or ForeignItems dispatch is
needed to construct this family. -/
def sourceHooks (foreign : ForeignItems.Core Provenance S D (MPlaceTy Provenance)
    (Pointer (Option Provenance)) B I) (random : RandomMemory.Hooks S)
    (signature : String → M S (FnAbi TyId))
    (errnoNegOne : String → MPlaceTy Provenance → M S Unit)
    (writeTargetUsize : UInt64 → MPlaceTy Provenance → M S Unit) : Hooks S D B I :=
  {
    random
    signatures := ⟨foreign⟩
    signature
    readPointer := foreign.readPointer
    readUsize := foreign.readUsize
    readI32 := foreign.readI32
    errnoNegOne
    writeNull := foreign.writeNull
    writeTargetUsize
  }
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked random shim argument absent")

def emulate (h : Hooks S D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless #["getentropy","getrandom","arc4random_buf"].contains name do return none
  let allowed := if name == "getentropy" then #["linux","macos","freebsd","illumos","solaris","android"]
    else if name == "getrandom" then #["linux","freebsd","illumos","solaris","android"]
    else #["freebsd","illumos","solaris"]
  unless allowed.contains h.signatures.foreign.os do
    throw (.unsupported "random shim unavailable on target OS")
  let args ← ShimSignatures.fixedCore h.signatures name (h.signature name)
    (if name == "getrandom" then 3 else 2) abi args
  let pointer ← h.readPointer (← arg args 0)
  let length ← h.readUsize (← arg args 1)
  if name == "getentropy" then
    if length > 256 then h.errnoNegOne "EIO" dest else
      RandomMemory.generate h.random pointer length
      h.writeNull dest
  else if name == "getrandom" then
    let _ ← h.readI32 (← arg args 2)
    RandomMemory.generate h.random pointer length
    h.writeTargetUsize length dest
  else
    RandomMemory.generate h.random pointer length
  return some .NeedsReturn

def dispatch (h : Hooks S D B I)
    (other : String → FnAbi TyId → Array (OpTy Provenance) → MPlaceTy Provenance →
      M S ForeignItems.EmulateItemResult)
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S ForeignItems.EmulateItemResult := do
    if let some result ← emulate h name abi args dest then return result
    other name abi args dest
end Miri.Interpreter.UnixRandomDispatch
