import Miri.Interpreter.Math.Dispatch
import Miri.Interpreter.Intrinsics
import Miri.Interpreter.IntrinsicX86

namespace Miri.Interpreter.Math
open Miri.ABI Miri.Memory Miri.MIR

/-- Install the source ULP arithmetic in the already connected fast-float
intrinsic path, preserving every unrelated machine/compiler dictionary leaf. -/
def intrinsicHooks [PointerProvenance P] (h : Hooks P S C V) (base : IntrinsicHooks P S C V) : IntrinsicHooks P S C V :=
  { base with floatFastError := floatFastError h, mathHooks := some h }

/-- Full intrinsic entry point with concrete remaining math dispatch and the
existing scalar/memory/atomic/type-id/varargs/SIMD families. -/
def evalIntrinsics [PointerProvenance P] (h : Hooks P S C V) (base : IntrinsicHooks P S C V)
    (choice : C) (name : String) (types : Array TyId) (args : Array (OpTy P)) (dest : V)
    (ret : Option BasicBlockId) : M S Bool := do
  if ← evalIntrinsic h choice name types args dest then
    h.returnToBlock choice ret
    return true
  Intrinsics.eval (intrinsicHooks h base) choice name types args dest ret

/-- Close x86 rsqrt's previous sqrt leaf with the portable bit-by-bit algorithm;
its source relative-error machinery and all other x86 operations remain intact. -/
def x86Hooks (h : Hooks P S C V) (base : IntrinsicX86.Hooks P S C V) : IntrinsicX86.Hooks P S C V :=
  { base with
    sqrt := fun _ value => engine (sqrt value)
    floatNondet := h.floatOps.floatNondeterministic
    roundingError := match h.errorMode with | .none => .none | .random => .random | .max => .max
    errorMagnitude := h.relativeMagnitude
    errorNegative := h.relativeNegative }

/-- Canonical SIMD math-lane binding. The source f128 host-unary unsupported
arm remains visible; sqrt supports f128 without a host approximation. -/
def simdMathLane [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (op : SimdMathOp) (source : OpTy P) (dest : V) : M S Unit := do
  let format ← h.floatOps.formatOf choice source.layout.ty
  if op == .sqrt then
    let value ← readFloat h choice source format
    let result ← engine (sqrt value)
    let result ← FloatOps.adjustNaN h.floatOps choice result [value]
    writeFloat h choice result dest
  else
    if format == .binary128 then throw (.unsupported "source f128 host unary operation is unimplemented")
    let value ← readFloat h choice source format
    let (name,operation) ← match op with
      | .sin => pure ("sin",Unary.sin) | .cos => pure ("cos",.cos) | .exp => pure ("exp",.exp) | .exp2 => pure ("exp2",.exp2)
      | .log => pure ("log",.log) | .log2 => pure ("log2",.log2) | .log10 => pure ("log10",.log10)
      | .sqrt => throw (.invalidProgram "sqrt must use portable square-root path")
    writeFloat h choice (← runUnary h choice name operation value) dest

end Miri.Interpreter.Math
