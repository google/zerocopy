import Miri.Interpreter.Math.Fixed

namespace Miri.Interpreter.Math
open Miri.ABI Miri.Memory Miri.MIR

def unaryName : String → Option Unary
  | "sin" => some .sin | "cos" => some .cos | "exp" => some .exp | "exp2" => some .exp2
  | "log" => some .log | "log10" => some .log10 | "log2" => some .log2
  | "cbrt" => some .cbrt | "cosh" => some .cosh | "sinh" => some .sinh | "tan" => some .tan | "tanh" => some .tanh
  | "acos" => some .acos | "asin" => some .asin | "atan" => some .atan | "acosh" => some .acosh | "asinh" => some .asinh
  | "log1p" => some .log1p | "expm1" => some .expm1 | "tgamma" => some .tgamma | "erf" => some .erf | "erfc" => some .erfc
  | _ => none

def runUnary (h : Hooks P S C V) (choice : C) (name : String) (op : Unary) (value : FloatBits) : M S FloatBits := do
  let result ← match ← fixedValue h choice value.format name [value] with
    | some result => pure result
    | none =>
      let raw ← liftResult (toHost value)
      let result ← h.hostUnary choice op raw
      let result ← hostResult value.format result
      let result ← applyUlpError h choice result 4
      clamp name result
  FloatOps.adjustNaN h.floatOps choice result [value]

def runBinary (h : Hooks P S C V) (choice : C) (name : String) (op : Binary)
    (a b : FloatBits) (clampResult : Bool) : M S FloatBits := do
  let result ← match ← fixedValue h choice a.format name [a,b] with
    | some result => pure result
    | none =>
      let aHost ← liftResult (toHost a)
      let bHost ← liftResult (toHost b)
      let result ← h.hostBinary choice op aHost bHost
      let result ← hostResult a.format result
      let result ← applyUlpError h choice result 4
      if clampResult then clamp name result else pure result
  FloatOps.adjustNaN h.floatOps choice result [a,b]

def floatFastError [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (value : RvalueImmTy P) (bound : Nat) : M S (RvalueImmTy P) := do
  -- Source to_scalar_int rejects size mismatch before the compiler float kind query.
  let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
  let integer ← scalarResult scalar.toScalarInt
  let _ ← liftResult (integer.toBits value.layout.layout.size |>.mapError ScalarOps.scalarIntError)
  let format ← h.floatOps.formatOf choice value.layout.ty
  unless format.size == value.layout.layout.size do invalid "float error operand layout mismatch"
  let valueBits : FloatBits := ⟨format,integer.toBitsUnchecked⟩
  let result ← applyUlpError h choice valueBits bound
  let scalar ← scalarResult (Memory.Scalar.fromUInt result.bits result.format.size)
  pure ⟨.scalar scalar,value.layout⟩

private def parseFormat (name : String) : Option FloatFormat :=
  if name.endsWith "f16" then some .binary16 else if name.endsWith "f32" then some .binary32
  else if name.endsWith "f64" then some .binary64 else if name.endsWith "f128" then some .binary128 else none

/-- All remaining source math intrinsic arms. Host f128 preserves the pinned
unimplemented arm; sqrtf128 uses the fully portable integer algorithm. -/
def evalIntrinsic [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (name : String) (generics : Array TyId) (args : Array (OpTy P)) (dest : V) : M S Bool := do
  if ["sqrtf16","sqrtf32","sqrtf64","sqrtf128"].contains name then
    arity args 1
    let some format := parseFormat name | invalid "sqrt format assertion"
    let value ← readFloat h choice (← arg args 0) format
    let result ← engine (sqrt value)
    let result ← FloatOps.adjustNaN h.floatOps choice result [value]
    writeFloat h choice result dest
  else if ["sin","cos","exp","exp2","log","log10","log2"].contains name then
    let some op := unaryName name | invalid "host unary operation assertion"
    let format ← h.genericFloat choice generics
    arity args 1
    if format == .binary128 then throw (.unsupported "source host math f128 is unimplemented")
    let value ← readFloat h choice (← arg args 0) format
    writeFloat h choice (← runUnary h choice name op value) dest
  else if ["powf16","powf32","powf64","powf128","powif16","powif32","powif64","powif128"].contains name then
    let some format := parseFormat name | invalid "pow format assertion"
    if format == .binary128 then throw (.unsupported "source host pow f128 is unimplemented")
    arity args 2
    let value ← readFloat h choice (← arg args 0) format
    if name.startsWith "powi" then
      let power ← scalarResult ((← readScalar h choice (← arg args 1)).toInt32)
      let result ← match ← fixedPowi h choice value power with
        | some result => pure result
        | none =>
          let raw ← liftResult (toHost value)
          let result ← h.hostPowi choice raw power
          let result ← hostResult format result
          applyUlpError h choice result 4
      let result ← FloatOps.adjustNaN h.floatOps choice result [value]
      writeFloat h choice result dest
    else
      let power ← readFloat h choice (← arg args 1) format
      writeFloat h choice (← runBinary h choice "pow" .pow value power false) dest
  else if ["fadd_fast","fsub_fast","fmul_fast","fdiv_fast","frem_fast"].contains name then
    arity args 2
    let a ← h.readImmediate choice (← arg args 0)
    let b ← h.readImmediate choice (← arg args 1)
    let aBits ← FloatOps.readBits h.floatOps choice a
    let aFinite ← engine (isFinite aBits)
    let bBits ← FloatOps.readBits h.floatOps choice b
    let bFinite ← engine (isFinite bBits)
    if !aFinite && !bFinite then throw (.undefinedBehavior "fast float intrinsic has non-finite values as both parameters")
    if !aFinite then throw (.undefinedBehavior "fast float intrinsic has non-finite first parameter")
    if !bFinite then throw (.undefinedBehavior "fast float intrinsic has non-finite second parameter")
    let op := match name with | "fadd_fast" => BinOp.Add | "fsub_fast" => .Sub | "fmul_fast" => .Mul | "fdiv_fast" => .Div | _ => .Rem
    let result ← ScalarOps.binary h.scalarOps choice op a b
    let bits ← FloatOps.readBits h.floatOps choice result
    unless ← engine (isFinite bits) do throw (.undefinedBehavior "fast float intrinsic produced non-finite result")
    let result ← floatFastError h choice result 4
    h.writeImmediate choice result.imm dest
  else if name == "float_to_int_unchecked" then
    arity args 1
    let source ← h.readImmediate choice (← arg args 0)
    let value ← FloatOps.readBits h.floatOps choice source
    let layout := h.destLayout dest
    let kind ← h.floatOps.integerKindOf choice layout.ty
    let width ← liftResult (layout.layout.size.bitsNat.mapError fun error => .invalidProgram s!"{reprStr error}")
    let some result ← engine (IntrinsicFloat.toIntegerChecked value width kind.signed)
      | throw (.undefinedBehavior "float_to_int_unchecked cannot represent input in target type")
    let scalar ← if kind.signed then scalarResult (Memory.Scalar.fromInt result layout.layout.size)
      else scalarResult (Memory.Scalar.fromUInt (BitVec.ofInt 128 result) layout.layout.size)
    h.writeImmediate choice (.scalar scalar) dest
  else return false
  return true

private def cSignature (h : Hooks P S C V) (choice : C) (name : String) (args : Array (OpTy P)) (count : Nat) : M S Unit := do
  h.checkCSignature choice name count
  unless args.size == count do throw (.undefinedBehavior "incorrect number of C math shim arguments")

/-- Full shims/math.rs dispatch. Gamma's sign pointer is dereferenced before
host evaluation and written before error perturbation/clamping/NaN choice. -/
def evalShim [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) : M S Bool := do
  let unaryF32 := ["cbrtf","coshf","sinhf","tanf","tanhf","acosf","asinf","atanf","acoshf","asinhf","log1pf","expm1f","tgammaf","erff","erfcf"].contains name
  let unaryF64 := ["cbrt","cosh","sinh","tan","tanh","acos","asin","atan","acosh","asinh","log1p","expm1","tgamma","erf","erfc"].contains name
  let binaryF32 := ["_hypotf","hypotf","atan2f","fdimf"].contains name
  let binaryF64 := ["_hypot","hypot","atan2","fdim"].contains name
  if unaryF32 || unaryF64 then
    cSignature h choice name args 1
    let format := if unaryF32 then FloatFormat.binary32 else .binary64
    let some op := unaryName (stripSuffix name) | invalid "libc unary math operation assertion"
    let value ← readFloat h choice (← arg args 0) format
    writeFloat h choice (← runUnary h choice name op value) dest
  else if binaryF32 || binaryF64 then
    cSignature h choice name args 2
    let format := if binaryF32 then FloatFormat.binary32 else .binary64
    let a ← readFloat h choice (← arg args 0) format
    let b ← readFloat h choice (← arg args 1) format
    let op := match stripSuffix name with | "_hypot" | "hypot" => Binary.hypot | "atan2" => .atan2 | _ => .fdim
    writeFloat h choice (← runBinary h choice name op a b true) dest
  else if ["_ldexp","ldexp","scalbn"].contains name then
    cSignature h choice name args 2
    let value ← readFloat h choice (← arg args 0) .binary64
    let exp ← scalarResult ((← readScalar h choice (← arg args 1)).toInt32)
    let result ← engine (scalbn value exp.toInt)
    let result ← FloatOps.adjustNaN h.floatOps choice result [value]
    writeFloat h choice result dest
  else if name == "lgammaf_r" || name == "lgamma_r" then
    cSignature h choice name args 2
    let format := if name == "lgammaf_r" then FloatFormat.binary32 else .binary64
    let value ← readFloat h choice (← arg args 0) format
    let signPlace ← h.derefI32 choice (← arg args 1)
    let host ← liftResult (toHost value)
    let (result,sign) ← h.hostLgamma choice host
    h.writeI32 choice sign signPlace
    let result ← hostResult format result
    let result ← applyUlpError h choice result 4
    let result ← clamp name result
    let result ← FloatOps.adjustNaN h.floatOps choice result [value]
    writeFloat h choice result dest
  else return false
  return true

end Miri.Interpreter.Math
