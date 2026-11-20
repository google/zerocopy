import Miri.Interpreter.RandomMemory
import Miri.Interpreter.ShimSignatures

/-! Exact Windows foreign_items.rs entropy arms. Unsupported BCrypt algorithm
and flag combinations remain Unsupported, matching source rather than UB. -/
namespace Miri.Interpreter.WindowsRandomDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Hooks (S D B I : Type) where
  random : RandomMemory.Hooks S
  signatures : ShimSignatures.CoreHooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  signature : String → M S (FnAbi TyId)
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readUsize : OpTy Provenance → M S UInt64
  readU32 : OpTy Provenance → M S UInt32
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writeNull : MPlaceTy Provenance → M S Unit

/-- Construct the Windows entropy family from nonrecursive source primitives;
the signature query and result writers remain the exact compiler/machine
effects supplied by the caller. -/
def sourceHooks (foreign : ForeignItems.Core Provenance S D (MPlaceTy Provenance)
    (Pointer (Option Provenance)) B I) (random : RandomMemory.Hooks S)
    (signature : String → M S (FnAbi TyId))
    (readU32 : OpTy Provenance → M S UInt32)
    (writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit)
    (writeInt : Int → MPlaceTy Provenance → M S Unit) : Hooks S D B I := {
  random
  signatures := ⟨foreign⟩
  signature
  readPointer := foreign.readPointer
  readUsize := foreign.readUsize
  readU32
  writeScalar
  writeInt
  writeNull := foreign.writeNull
}
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked Windows random argument absent")

def emulate (h : Hooks S D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless #["SystemFunction036","ProcessPrng","BCryptGenRandom"].contains name do return none
  let args ← ShimSignatures.fixedCore h.signatures name (h.signature name)
    (if name == "BCryptGenRandom" then 4 else 2) abi args
  if name == "BCryptGenRandom" then
    let algorithm ← h.readUsize (← arg args 0)
    let pointer ← h.readPointer (← arg args 1)
    let length ← h.readU32 (← arg args 2)
    let flags ← h.readU32 (← arg args 3)
    if flags == 0 then
      unless algorithm == 0x81 do throw (.unsupported "BCryptGenRandom requires BCRYPT_RNG_ALG_HANDLE")
    else if flags == 2 then
      unless algorithm == 0 do throw (.unsupported "BCryptGenRandom system preferred RNG requires NULL")
    else throw (.unsupported "BCryptGenRandom unsupported flags")
    RandomMemory.generate h.random pointer (UInt64.ofNat length.toNat)
    h.writeNull dest
  else
    let pointer ← h.readPointer (← arg args 0)
    let length ← if name == "SystemFunction036" then do
        let value ← h.readU32 (← arg args 1)
        pure (UInt64.ofNat value.toNat)
      else h.readUsize (← arg args 1)
    RandomMemory.generate h.random pointer length
    if name == "SystemFunction036" then
      let value := Scalar.fromBool true
      h.writeScalar value dest
    else h.writeInt 1 dest
  return some .NeedsReturn

def dispatch (h : Hooks S D B I)
    (other : String → FnAbi TyId → Array (OpTy Provenance) → MPlaceTy Provenance →
      M S ForeignItems.EmulateItemResult)
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S ForeignItems.EmulateItemResult := do
  if let some result ← emulate h name abi args dest then return result
  other name abi args dest
end Miri.Interpreter.WindowsRandomDispatch
