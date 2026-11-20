import Miri.Input.EvalMathMachine

/-! Host-backed source math capabilities implemented by Lean's actual
binary32/binary64 C math bindings. Bits cross the boundary unchanged; the
source math interpreter remains responsible for NaN adjustment and the
configured error perturbation. Unsupported source widths and operations stay
visible at the exact host callback that requests them. -/
namespace Miri.Input.NativeMathHost
open Miri.Interpreter

/-! Lean's bundled Float API exposes only a subset of libc's C math functions.
These direct scalar externs use the Linux libc symbols called by pinned
`std::num::{f32,f64}` on the required Linux host. -/
@[extern "expm1f"] private opaque expm1f (value : Float32) : Float32
@[extern "log1pf"] private opaque log1pf (value : Float32) : Float32
@[extern "tgammaf"] private opaque tgammaf (value : Float32) : Float32
@[extern "erff"] private opaque erff (value : Float32) : Float32
@[extern "erfcf"] private opaque erfcf (value : Float32) : Float32
@[extern "hypotf"] private opaque hypotf (left right : Float32) : Float32
@[extern "fdimf"] private opaque fdimf (left right : Float32) : Float32

@[extern "expm1"] private opaque expm1 (value : Float) : Float
@[extern "log1p"] private opaque log1p (value : Float) : Float
@[extern "tgamma"] private opaque tgamma (value : Float) : Float
@[extern "erf"] private opaque erf (value : Float) : Float
@[extern "erfc"] private opaque erfc (value : Float) : Float
@[extern "hypot"] private opaque hypot (left right : Float) : Float
@[extern "fdim"] private opaque fdim (left right : Float) : Float
@[extern "lean_miri_lgammaf_r"] private opaque lgammafR (value : Float32) : Float32 × Int32
@[extern "lean_miri_lgamma_r"] private opaque lgammaR (value : Float) : Float × Int32

private def unsupported {S A : Type} (message : String) : RvalueM S A :=
  throw (.unsupported message)

private def unary32 (operation : Math.Unary) (value : Float32) : Option Float32 :=
  match operation with
  | .sin => some value.sin
  | .cos => some value.cos
  | .exp => some value.exp
  | .exp2 => some value.exp2
  | .log => some value.log
  | .log10 => some value.log10
  | .log2 => some value.log2
  | .expm1 => some (expm1f value)
  | .log1p => some (log1pf value)
  | .cbrt => some value.cbrt
  | .cosh => some value.cosh
  | .sinh => some value.sinh
  | .tan => some value.tan
  | .tanh => some value.tanh
  | .acos => some value.acos
  | .asin => some value.asin
  | .atan => some value.atan
  | .acosh => some value.acosh
  | .asinh => some value.asinh
  | .tgamma => some (tgammaf value)
  | .erf => some (erff value)
  | .erfc => some (erfcf value)

private def unary64 (operation : Math.Unary) (value : Float) : Option Float :=
  match operation with
  | .sin => some value.sin
  | .cos => some value.cos
  | .exp => some value.exp
  | .exp2 => some value.exp2
  | .log => some value.log
  | .log10 => some value.log10
  | .log2 => some value.log2
  | .expm1 => some (expm1 value)
  | .log1p => some (log1p value)
  | .cbrt => some value.cbrt
  | .cosh => some value.cosh
  | .sinh => some value.sinh
  | .tan => some value.tan
  | .tanh => some value.tanh
  | .acos => some value.acos
  | .asin => some value.asin
  | .atan => some value.atan
  | .acosh => some value.acosh
  | .asinh => some value.asinh
  | .tgamma => some (tgamma value)
  | .erf => some (erf value)
  | .erfc => some (erfc value)

private def binary32 (operation : Math.Binary) (left right : Float32) : Option Float32 :=
  match operation with
  | .pow => some (left.pow right)
  | .hypot => some (hypotf left right)
  | .atan2 => some (left.atan2 right)
  | .fdim => some (fdimf left right)

private def binary64 (operation : Math.Binary) (left right : Float) : Option Float :=
  match operation with
  | .pow => some (left.pow right)
  | .hypot => some (hypot left right)
  | .atan2 => some (left.atan2 right)
  | .fdim => some (fdim left right)

private def binary16 (operation : Math.Binary) (left right : Float32) : Option Float32 :=
  match operation with
  | .pow | .hypot | .atan2 => binary32 operation left right
  | _ => none

private def one32 : Float32 := Float32.ofBits 0x3f800000
private def one64 : Float := Float.ofBits 0x3ff0000000000000

/-- Pinned compiler-builtins `float/pow.rs::pow` operation order, using each
host-width multiplication/division exactly once per source iteration. -/
private def powi32 (base : Float32) (exponent : Int32) : Float32 := Id.run do
  let signedExponent := exponent.toInt
  let mut remaining := if signedExponent < 0 then (-signedExponent).toNat else signedExponent.toNat
  let mut factor := base
  let mut product := one32
  while remaining != 0 do
    if remaining % 2 != 0 then product := product * factor
    remaining := remaining / 2
    if remaining != 0 then factor := factor * factor
  if signedExponent < 0 then return one32 / product
  return product

private def powi64 (base : Float) (exponent : Int32) : Float := Id.run do
  let signedExponent := exponent.toInt
  let mut remaining := if signedExponent < 0 then (-signedExponent).toNat else signedExponent.toNat
  let mut factor := base
  let mut product := one64
  while remaining != 0 do
    if remaining % 2 != 0 then product := product * factor
    remaining := remaining / 2
    if remaining != 0 then factor := factor * factor
  if signedExponent < 0 then return one64 / product
  return product

private def liftFloatError {S A : Type} (value : Except FloatError A) : RvalueM S A :=
  match value with
  | .ok result => pure result
  | .error error => throw (.invalidProgram s!"host float-width conversion: {reprStr error}")

private def halfToSingleBits {S : Type} (bits : BitVec 16) : RvalueM S Float32 := do
  let half : FloatBits := ⟨.binary16, BitVec.ofNat 128 bits.toNat⟩
  let single ← liftFloatError (half.convert .binary32)
  pure (Float32.ofBits (UInt32.ofNat single.bits.toNat))

private def singleToHalfBits {S : Type} (value : Float32) : RvalueM S (BitVec 16) := do
  let single : FloatBits := ⟨.binary32, BitVec.ofNat 128 value.toBits.toNat⟩
  let half ← liftFloatError (single.convert .binary16)
  pure (BitVec.ofNat 16 half.bits.toNat)

private def powi {S : Type} (base : Math.HostBits) (exponent : Int32) : RvalueM S Math.HostBits := do
  match base with
  | .single bits =>
    let result := powi32 (Float32.ofBits (UInt32.ofNat bits.toNat)) exponent
    pure (.single (BitVec.ofNat 32 result.toBits.toNat))
  | .double bits =>
    let result := powi64 (Float.ofBits (UInt64.ofNat bits.toNat)) exponent
    pure (.double (BitVec.ofNat 64 result.toBits.toNat))
  | .half bits =>
    let base ← halfToSingleBits bits
    let result ← singleToHalfBits (powi32 base exponent)
    pure (.half result)

private def unary {S : Type} (operation : Math.Unary) (value : Math.HostBits) : RvalueM S Math.HostBits := do
  match value with
  | .single bits =>
    match unary32 operation (Float32.ofBits (UInt32.ofNat bits.toNat)) with
    | some result => pure (.single (BitVec.ofNat 32 result.toBits.toNat))
    | none => unsupported s!"native binary32 host math operation {reprStr operation} is unavailable"
  | .double bits =>
    match unary64 operation (Float.ofBits (UInt64.ofNat bits.toNat)) with
    | some result => pure (.double (BitVec.ofNat 64 result.toBits.toNat))
    | none => unsupported s!"native binary64 host math operation {reprStr operation} is unavailable"
  | .half bits => do
    let value ← halfToSingleBits bits
    match unary32 operation value with
    | some result => pure (.half (← singleToHalfBits result))
    | none => unsupported s!"native binary16 host math operation {reprStr operation} is unavailable"

private def binary {S : Type} (operation : Math.Binary) (left right : Math.HostBits) : RvalueM S Math.HostBits := do
  match left, right with
  | .single left, .single right =>
    match binary32 operation (Float32.ofBits (UInt32.ofNat left.toNat)) (Float32.ofBits (UInt32.ofNat right.toNat)) with
    | some result => pure (.single (BitVec.ofNat 32 result.toBits.toNat))
    | none => unsupported s!"native binary32 host math operation {reprStr operation} is unavailable"
  | .double left, .double right =>
    match binary64 operation (Float.ofBits (UInt64.ofNat left.toNat)) (Float.ofBits (UInt64.ofNat right.toNat)) with
    | some result => pure (.double (BitVec.ofNat 64 result.toBits.toNat))
    | none => unsupported s!"native binary64 host math operation {reprStr operation} is unavailable"
  | .half left, .half right => do
    let left ← halfToSingleBits left
    let right ← halfToSingleBits right
    match binary16 operation left right with
    | some result => pure (.half (← singleToHalfBits result))
    | none => unsupported s!"native binary16 host math operation {reprStr operation} is unavailable"
  | _, _ => unsupported "native host math received operands with different float widths"

private def lgamma {S : Type} (base : Math.HostBits) : RvalueM S (Math.HostBits × Int32) := do
  match base with
  | .single bits =>
    let (result, sign) := lgammafR (Float32.ofBits (UInt32.ofNat bits.toNat))
    pure (.single (BitVec.ofNat 32 result.toBits.toNat), sign)
  | .double bits =>
    let (result, sign) := lgammaR (Float.ofBits (UInt64.ofNat bits.toNat))
    pure (.double (BitVec.ofNat 64 result.toBits.toNat), sign)
  | .half bits => do
    let value ← halfToSingleBits bits
    let (result, sign) := lgammafR value
    pure (.half (← singleToHalfBits result), sign)

/-- Adapter for real Linux host math operations. Binary16 paths are enabled
only where pinned core/std promotes to a corresponding f32 operation. -/
def host (S C : Type) : EvalMathMachine.Host S C where
  unary := fun _ operation value => unary operation value
  binary := fun _ operation left right => binary operation left right
  powi := fun _ value exponent => powi value exponent
  lgamma := fun _ value => lgamma value

end Miri.Input.NativeMathHost
