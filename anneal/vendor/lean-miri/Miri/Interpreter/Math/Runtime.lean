import Miri.Interpreter.Math.Float

namespace Miri.Interpreter.Math
open Miri.ABI Miri.Memory Miri.MIR

inductive ErrorMode where
  | none | random | max
  deriving DecidableEq, Repr
inductive Unary where
  | sin | cos | exp | exp2 | log | log10 | log2
  | cbrt | cosh | sinh | tan | tanh | acos | asin | atan | acosh | asinh | log1p | expm1 | tgamma | erf | erfc
  deriving DecidableEq, Repr
inductive Binary where
  | pow | hypot | atan2 | fdim
  deriving DecidableEq, Repr

/-- Actual host f16/f32/f64 bit representations; conversion is bit identity,
never an intermediate Lean Float or an implicit promotion to binary64. -/
inductive HostBits where
  | half (bits : BitVec 16) | single (bits : BitVec 32) | double (bits : BitVec 64)
  deriving DecidableEq, Repr

def HostBits.toSoft : HostBits → FloatBits
  | .half bits => ⟨.binary16, BitVec.ofNat 128 bits.toNat⟩
  | .single bits => ⟨.binary32, BitVec.ofNat 128 bits.toNat⟩
  | .double bits => ⟨.binary64, BitVec.ofNat 128 bits.toNat⟩

def toHost (value : FloatBits) : Except StepError HostBits := do
  let _ ← value.decode.mapError fun error => .invalidProgram s!"host float input: {reprStr error}"
  match value.format with
  | .binary16 => pure (.half (BitVec.ofNat 16 value.bits.toNat))
  | .binary32 => pure (.single (BitVec.ofNat 32 value.bits.toNat))
  | .binary64 => pure (.double (BitVec.ofNat 64 value.bits.toNat))
  | .binary128 => throw (.unsupported "source host math f128 is unimplemented")

structure Hooks (P S C V : Type) where
  floatOps : FloatOpsHooks P S C
  scalarOps : ScalarOpsHooks P S C
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  writeImmediate : C → Immediate P → V → RvalueM S Unit
  destLayout : V → TyAndLayout TyId
  genericFloat : C → Array TyId → RvalueM S FloatFormat
  /-- Source C ABI/deprecated shim argument check; compiler call ABI retained. -/
  checkCSignature : C → String → Nat → RvalueM S Unit
  derefI32 : C → OpTy P → RvalueM S V
  writeI32 : C → Int32 → V → RvalueM S Unit
  hostUnary : C → Unary → HostBits → RvalueM S HostBits
  hostBinary : C → Binary → HostBits → HostBits → RvalueM S HostBits
  hostPowi : C → HostBits → Int32 → RvalueM S HostBits
  hostLgamma : C → HostBits → RvalueM S (HostBits × Int32)
  errorMode : ErrorMode
  ulpError : C → Nat → RvalueM S Int
  maxErrorPositive : C → RvalueM S Bool
  relativeMagnitude : C → Nat → RvalueM S Nat
  relativeNegative : C → RvalueM S Bool
  snanPowNaN : C → RvalueM S Bool
  returnToBlock : C → Option BasicBlockId → RvalueM S Unit

abbrev M (S A : Type) := RvalueM S A

def liftResult (result : Except StepError A) : M S A :=
  match result with | .ok value => pure value | .error error => throw error
def engine (result : Except FloatError A) : M S A :=
  liftResult (result.mapError fun error => .invalidProgram s!"source math float: {reprStr error}")
def invalid (message : String) : M S A := throw (.invalidProgram message)
def scalarResult (result : Except ScalarError A) : M S A := liftResult (result.mapError ScalarOps.scalarError)
def arity (args : Array (OpTy P)) (count : Nat) : M S Unit :=
  unless args.size == count do throw (.undefinedBehavior "incorrect number of arguments for intrinsic")
def arg (args : Array (OpTy P)) (i : Nat) : M S (OpTy P) :=
  match args[i]? with | some op => pure op | none => invalid "math argument missing"
def readScalar (h : Hooks P S C V) (choice : C) (op : OpTy P) : M S (Memory.Scalar P) := do
  let value ← h.readImmediate choice op
  liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
def readFloat [PointerProvenance P] (h : Hooks P S C V) (choice : C) (op : OpTy P) (format : FloatFormat) : M S FloatBits := do
  let bits ← scalarResult ((← readScalar h choice op).toBits format.size)
  let value : FloatBits := ⟨format,bits⟩
  let _ ← engine value.decode
  pure value

def writeFloat (h : Hooks P S C V) (choice : C) (value : FloatBits) (dest : V) : M S Unit := do
  let scalar ← scalarResult (Memory.Scalar.fromUInt value.bits value.format.size)
  h.writeImmediate choice (.scalar scalar) dest

def hostResult (expected : FloatFormat) (result : HostBits) : M S FloatBits := do
  let result := result.toSoft
  unless result.format == expected do invalid "host math returned a different float width"
  pure result

def applyUlpError (h : Hooks P S C V) (choice : C) (value : FloatBits) (bound : Nat) : M S FloatBits := do
  if !h.floatOps.floatNondeterministic || h.errorMode == .none then return value
  if ← engine (isZero value) then return value
  unless ← engine (isFinite value) do return value
  if bound >= 2^32 then invalid "source ULP bound does not fit u32"
  let error ← if h.errorMode == .max then do
      let positive ← h.maxErrorPositive choice
      pure (if positive then Int.ofNat bound else -(Int.ofNat bound))
    else h.ulpError choice bound
  unless -(Int.ofNat bound) <= error && error <= Int.ofNat bound do invalid "illegal source ULP error choice"
  let up ← engine (nextUp value)
  let down ← engine (nextDown value)
  let a ← engine (FloatBits.arithmetic .Sub up value)
  let b ← engine (FloatBits.arithmetic .Sub value down)
  let sum ← engine (FloatBits.arithmetic .Add a b)
  let two ← engine (FloatBits.fromInteger value.format 2)
  let ulp ← engine (FloatBits.arithmetic .Div sum two)
  let error ← engine (FloatBits.fromInteger value.format error)
  let delta ← engine (FloatBits.arithmetic .Mul ulp error)
  engine (FloatBits.arithmetic .Add value delta)

def applyRelativeError (h : Hooks P S C V) (choice : C) (value : FloatBits) (scale : Int32) : M S FloatBits := do
  if !h.floatOps.floatNondeterministic || h.errorMode == .none then return value
  if ← engine (isZero value) then return value
  unless ← engine (isFinite value) do return value
  let precision := value.format.fractionBits+1
  let magnitude ← if h.errorMode == .max then pure (2^precision-1) else h.relativeMagnitude choice precision
  if magnitude >= 2^precision then invalid "illegal source relative error magnitude"
  let r ← engine (FloatBits.fromInteger value.format (Int.ofNat magnitude))
  let power := scale.toInt-Int.ofNat precision
  unless -(2^31 : Int) <= power && power < 2^31 do invalid "relative error scale subtraction overflow"
  let err ← engine (scalbn r power)
  let err ← if ← h.relativeNegative choice then engine err.negate else pure err
  let product ← engine (FloatBits.arithmetic .Mul value err)
  engine (FloatBits.arithmetic .Add value product)

end Miri.Interpreter.Math
