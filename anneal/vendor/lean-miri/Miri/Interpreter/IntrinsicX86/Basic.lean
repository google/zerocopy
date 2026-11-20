import Miri.Interpreter.IntrinsicArchitecture

namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

inductive FloatErrorMode where
  | none | random | max
  deriving DecidableEq, Repr

structure Hooks (P S C V : Type) where
  architecture : ArchitectureHooks P S C V
  x86_64 : Bool
  sse2Enabled : Bool
  yieldThread : C → RvalueM S Unit
  arrayLayout : C → TyId → UInt64 → RvalueM S (TyAndLayout TyId)
  integerLayout : C → Nat → Bool → RvalueM S (TyAndLayout TyId)
  transmuteRead : C → OpTy P → TyAndLayout TyId → RvalueM S (OpTy P)
  transmuteWrite : C → V → TyAndLayout TyId → RvalueM S V
  twiceWideLayout : C → TyId → RvalueM S (TyAndLayout TyId)
  /-- Source uses host sqrt for rsqrt; this is its explicit numerical boundary. -/
  sqrt : C → FloatBits → RvalueM S FloatBits
  floatNondet : Bool
  roundingError : FloatErrorMode
  errorMagnitude : C → Nat → RvalueM S Nat
  errorNegative : C → RvalueM S Bool
  memCopy : C → Pointer (Option P) → Pointer (Option P) → Size → Bool → RvalueM S Unit

abbrev M (S A : Type) := RvalueM S A

def invalid (message : String) : M S A := throw (.invalidProgram message)
def liftResult (result : Except StepError A) : M S A :=
  match result with | .ok value => pure value | .error error => throw error
def scalarResult (result : Except ScalarError A) : M S A := liftResult (result.mapError ScalarOps.scalarError)
def floatResult (result : Except FloatError A) : M S A :=
  liftResult (result.mapError fun error => .invalidProgram s!"x86 float: {reprStr error}")
def sizeResult (result : Except SizeError A) : M S A :=
  liftResult (result.mapError fun error => .invalidProgram s!"x86 size: {reprStr error}")
def arg (args : Array (OpTy P)) (i : Nat) : M S (OpTy P) :=
  match args[i]? with | some value => pure value | none => invalid "x86 argument missing"
def signature (h : Hooks P S C V) (choice : C) (name : String) (args : Array (OpTy P)) (n : Nat) : M S Unit := do
  unless name.startsWith "llvm." do invalid "LLVM signature helper prefix assertion"
  h.architecture.checkSignature choice name n
  unless args.size == n do throw (.undefinedBehavior "incorrect number of arguments for LLVM intrinsic")
def feature (h : Hooks P S C V) (choice : C) (name feature : String) : M S Unit :=
  h.architecture.expectFeature choice name feature
def scalar (value : RvalueImmTy P) : M S (Memory.Scalar P) :=
  liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
def read (h : Hooks P S C V) (choice : C) (op : OpTy P) : M S (Memory.Scalar P) := do
  scalar (← h.architecture.simd.readImmediate choice op)
def readLane (h : Hooks P S C V) (choice : C) (op : OpTy P) (i : UInt64) : M S (RvalueImmTy P) := do
  h.architecture.simd.readImmediate choice (← h.architecture.simd.indexRead choice op i)
def readScalarLane (h : Hooks P S C V) (choice : C) (op : OpTy P) (i : UInt64) : M S (Memory.Scalar P) := do
  read h choice (← h.architecture.simd.indexRead choice op i)
def write (h : Hooks P S C V) (choice : C) (value : Memory.Scalar P) (dest : V) : M S Unit :=
  h.architecture.simd.writeImmediate choice (.scalar value) dest
def length (layout : TyAndLayout TyId) : M S UInt64 :=
  match layout.layout.fields with | .Array _ n => pure n | _ => invalid "x86 SIMD backing field is not array"
def projectRead (h : Hooks P S C V) (choice : C) (op : OpTy P) : M S (OpTy P × UInt64) := do
  unless ← h.architecture.simd.isSimd choice op.layout.ty do invalid "x86 requires SIMD type"
  let array ← h.architecture.simd.fieldRead choice op 0
  pure (array, ← length array.layout)
def projectWrite (h : Hooks P S C V) (choice : C) (dest : V) : M S (V × UInt64) := do
  unless ← h.architecture.simd.isSimd choice (h.architecture.simd.placeLayout dest).ty do invalid "x86 requires SIMD type"
  let array ← h.architecture.simd.fieldWrite choice dest 0
  pure (array, ← length (h.architecture.simd.placeLayout array))
def same (a b : UInt64) : M S Unit := unless a == b do invalid "x86 vector length mismatch"
def checkedIndex (n : Nat) : M S UInt64 :=
  if n < 2^64 then pure (UInt64.ofNat n) else invalid "x86 strict index arithmetic overflow"
def fromUInt (value : Nat) (size : Size) : M S (Memory.Scalar P) :=
  scalarResult (Memory.Scalar.fromUInt (BitVec.ofNat 128 value) size)
def fromInt (value : Int) (size : Size) : M S (Memory.Scalar P) := scalarResult (Memory.Scalar.fromInt value size)
def truncInt (value : Int) (size : Size) : M S (Memory.Scalar P) := do
  let (integer, _) ← liftResult (ScalarInt.truncateFromInt value size |>.mapError ScalarOps.scalarIntError)
  pure (.fromScalarInt integer)
def makeImm (value : Int) (layout : TyAndLayout TyId) : M S (RvalueImmTy P) := do
  pure ⟨.scalar (← fromInt value layout.layout.size), layout⟩

def castInt [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (value : RvalueImmTy P) (dest : TyAndLayout TyId) : M S (RvalueImmTy P) := do
  let .integer kind ← h.architecture.simd.scalarOps.classify choice value.layout.ty
    | invalid "x86 integer cast source is not integer"
  let raw ← scalar value
  let result ← if kind.signed then do
    let n ← scalarResult (raw.toInt value.layout.layout.size)
    truncInt n dest.layout.size
    else do
      let n ← scalarResult (raw.toUInt value.layout.layout.size)
      let (integer, _) ← liftResult (ScalarInt.truncateFromUInt n dest.layout.size |>.mapError ScalarOps.scalarIntError)
      pure (.fromScalarInt integer)
  pure ⟨.scalar result, dest⟩

def splitRead (h : Hooks P S C V) (choice : C) (op : OpTy P) : M S (UInt64 × UInt64 × OpTy P) := do
  let (n, element) ← h.architecture.simd.simdSizeAndType choice op.layout.ty
  let bits ← sizeResult op.layout.layout.size.bits
  unless bits % 128 == 0 do invalid "x86 split requires multiple of 128 bits"
  let chunks := bits/128
  if chunks == 0 then invalid "x86 split strict division by zero"
  let perChunk := n/chunks
  let inner ← h.arrayLayout choice element perChunk
  let outer ← h.arrayLayout choice inner.ty chunks
  pure (chunks, perChunk, ← h.transmuteRead choice op outer)
def splitWrite (h : Hooks P S C V) (choice : C) (dest : V) : M S (UInt64 × UInt64 × V) := do
  let layout := h.architecture.simd.placeLayout dest
  let (n, element) ← h.architecture.simd.simdSizeAndType choice layout.ty
  let bits ← sizeResult layout.layout.size.bits
  unless bits % 128 == 0 do invalid "x86 split requires multiple of 128 bits"
  let chunks := bits/128
  if chunks == 0 then invalid "x86 split strict division by zero"
  let perChunk := n/chunks
  let inner ← h.arrayLayout choice element perChunk
  let outer ← h.arrayLayout choice inner.ty chunks
  pure (chunks, perChunk, ← h.transmuteWrite choice dest outer)

def copyRest (h : Hooks P S C V) (choice : C) (source : OpTy P) (dest : V) (n : UInt64) : M S Unit := do
  for i in [1:n.toNat] do
    let source ← h.architecture.simd.indexRead choice source (UInt64.ofNat i)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    h.architecture.simd.copyOp choice source dest

end Miri.Interpreter.IntrinsicX86
