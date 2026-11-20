import Miri.Interpreter.Math.Runtime
namespace Miri.Interpreter.Math
open Miri.ABI Miri.Memory Miri.MIR

def clamp (name : String) (value : FloatBits) : M S FloatBits := do
  let zero := FloatBits.zero value.format
  let one ← engine (FloatBits.fromInteger value.format 1)
  let two ← engine (FloatBits.fromInteger value.format 2)
  let pi ← liftResult (Math.pi value.format)
  let halfPi ← engine (FloatBits.arithmetic .Div pi two)
  let range := fun lo hi => do
    let value ← engine (extremum value lo true)
    engine (extremum value hi false)
  match stripSuffix name with
  | "sin" | "cos" | "tanh" | "erf" => range (← engine one.negate) one
  | "exp" | "exp2" => engine (extremum value zero true)
  | "cosh" => engine (extremum value one true)
  | "acos" => range zero pi
  | "asin" | "atan2" => range (← engine pi.negate) pi
  | "atan" => range (← engine halfPi.negate) halfPi
  | "erfc" => range zero two
  | _ => pure value

private def maybeSignalingNaN (h : Hooks P S C V) (choice : C) (format : FloatFormat)
    (value : FloatBits) (inputs : List FloatBits) (one : FloatBits) : M S FloatBits := do
  if ← engine value.isSignaling then
    if h.floatOps.floatNondeterministic then
      if ← h.snanPowNaN choice then
        return ← FloatOps.adjustNaN h.floatOps choice (FloatBits.preferredNaN format) inputs
  pure one

/-- Ordered C fixed-output cases from math.rs. In particular, the source's
atan2 guard tests nonzero/noninfinite x without adding an invented !isNaN test. -/
def fixedValue (h : Hooks P S C V) (choice : C) (format : FloatFormat)
    (name : String) (inputs : List FloatBits) : M S (Option FloatBits) := do
  let one ← engine (FloatBits.fromInteger format 1)
  let two ← engine (FloatBits.fromInteger format 2)
  let three ← engine (FloatBits.fromInteger format 3)
  let pi ← liftResult (Math.pi format)
  let halfPi ← engine (FloatBits.arithmetic .Div pi two)
  let quarterPi ← engine (FloatBits.arithmetic .Div halfPi two)
  let name := stripSuffix name
  match inputs with
  | [input] =>
    let zero ← engine (isZero input)
    let infinite ← engine (isInfinite input)
    if ["cos","cosh","exp","exp2"].contains name && zero then return some one
    if (name == "tanh" || name == "erf") && infinite then
      return some (← engine (IntrinsicFloat.copySign one input))
    if name == "atan" && infinite then return some (← engine (IntrinsicFloat.copySign halfPi input))
    if name == "erfc" && infinite then
      if ← engine (negative input) then return some (← engine (FloatBits.arithmetic .Add one one))
    return none
  | [x,y] =>
    let xZero ← engine (isZero x)
    let yZero ← engine (isZero y)
    let xInfinite ← engine (isInfinite x)
    let yInfinite ← engine (isInfinite y)
    let yNegative ← engine (negative y)
    if name == "_hypot" || name == "hypot" then
      if !(← engine x.isNaN) then
        if yZero then return some (← engine (IntrinsicFloat.abs x))
    if name == "atan2" then
      if xZero && yNegative then
        if !(← engine y.isNaN) then return some (← engine (IntrinsicFloat.copySign pi x))
      if !xZero && !xInfinite && yInfinite && yNegative then
        return some (← engine (IntrinsicFloat.copySign pi x))
      if !xZero && yZero then return some (← engine (IntrinsicFloat.copySign halfPi x))
      if xInfinite && yInfinite && yNegative then
        let result ← engine (FloatBits.arithmetic .Mul quarterPi three)
        return some (← engine (IntrinsicFloat.copySign result x))
      if xInfinite && yInfinite && !yNegative then
        return some (← engine (IntrinsicFloat.copySign quarterPi x))
      if xInfinite && !yInfinite then
        if !(← engine y.isNaN) then return some (← engine (IntrinsicFloat.copySign halfPi x))
    if name == "pow" then
      let negativeOne ← engine one.negate
      let xNegativeOne ← engine (x.comparison .Eq negativeOne)
      if xNegativeOne && yInfinite then return some one
      if ← engine (x.comparison .Eq one) then
        return some (← maybeSignalingNaN h choice format y inputs one)
      if yZero then return some (← maybeSignalingNaN h choice format x inputs one)
    return none
  | _ => pure none

def fixedPowi (h : Hooks P S C V) (choice : C) (value : FloatBits) (power : Int32) : M S (Option FloatBits) := do
  if power != 0 then return none
  let one ← engine (FloatBits.fromInteger value.format 1)
  pure (some (← maybeSignalingNaN h choice value.format value [value] one))

end Miri.Interpreter.Math
