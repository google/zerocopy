import Std

/-!
The machine-width size primitives from `rustc_abi::Size`.

The upstream source stores byte counts in `u64`, and stores integer values in
`u128`. Lean 4 has no `UInt128`, so `U128` is represented by `BitVec 128`;
this preserves the source machine width and wrapping behavior. Operations that
panic in upstream return an explicit `Except` error here.
-/

namespace Miri.ABI

/-! A structural equality decider for the standard `Except` result type. -/
instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := by
  intro left right
  cases left with
  | error l =>
      cases right with
      | error r =>
          if h : l = r then
            exact isTrue (congrArg Except.error h)
          else
            exact isFalse (fun eq => h (Except.error.inj eq))
      | ok r => exact isFalse (by intro eq; cases eq)
  | ok l =>
      cases right with
      | error r => exact isFalse (by intro eq; cases eq)
      | ok r =>
          if h : l = r then
            exact isTrue (congrArg Except.ok h)
          else
            exact isFalse (fun eq => h (Except.ok.inj eq))

abbrev U128 := BitVec 128

inductive Endian where
  | little
  | big
  deriving DecidableEq, Repr

namespace Endian

def asString : Endian → String
  | .little => "little"
  | .big => "big"

def parse (value : String) : Except String Endian :=
  match value with
  | "little" => .ok .little
  | "big" => .ok .big
  | _ => .error s!"unknown endian: \"{value}\""

end Endian

inductive PointerWidth where
  | w16
  | w32
  | w64
  deriving DecidableEq, Repr

namespace PointerWidth

def bits : PointerWidth → UInt64
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

def objSizeBound : PointerWidth → UInt64
  | .w16 => 32768
  | .w32 => 2147483648
  | .w64 => 2305843009213693952

end PointerWidth

/-! The relevant projection of rustc_abi's target-dependent data layout. -/
structure TargetDataLayout where
  endian : Endian
  pointerWidth : PointerWidth
  deriving DecidableEq, Repr

def TargetDataLayout.objSizeBound (layout : TargetDataLayout) : UInt64 :=
  layout.pointerWidth.objSizeBound

/-! The actual caller interface used by rustc_abi Size::checked_add/mul:
the caller supplies a data-layout value, from which the object-size bound is
read. -/
class HasDataLayout (α : Type) where
  dataLayout : α → TargetDataLayout

instance : HasDataLayout TargetDataLayout where
  dataLayout := id

inductive SizeError where
  | u64Overflow (operation : String) (left right : UInt64)
  | negativeSubtraction (left right : UInt64)
  | bitCountOverflow (bytes : UInt64)
  | integerWidthTooLarge (bits : UInt64)
  | zeroWidthUnsignedBound
  | zeroWidthSignedBound
  deriving Repr, DecidableEq

instance : ToString SizeError where
  toString
    | .u64Overflow operation left right =>
        s!"Size.{operation}: {left} and {right} do not fit in u64"
    | .negativeSubtraction left right =>
        s!"Size.sub: {left} - {right} would result in a negative size"
    | .bitCountOverflow bytes =>
        s!"Size.bits: {bytes} bytes in bits does not fit in u64"
    | .integerWidthTooLarge bits =>
        s!"integer width {bits} exceeds the u128 source width"
    | .zeroWidthUnsignedBound =>
        "unsigned integer maximum is undefined for a zero-bit integer"
    | .zeroWidthSignedBound =>
        "signed integer bounds are undefined for a zero-bit integer"

structure Size where
  bytes : UInt64
  deriving DecidableEq, Repr, Inhabited

namespace Size

def ZERO : Size := ⟨0⟩

@[inline] def ofBytes (bytes : UInt64) : Size := ⟨bytes⟩

@[inline] def fromBytes (bytes : UInt64) : Size := ofBytes bytes

/-! `div_ceil(8)` written without the overflowing `bits + 7` formulation. -/
@[inline] def fromBits (bits : UInt64) : Size :=
  let quotient := bits / 8
  let remainder := bits % 8
  ofBytes (quotient + if remainder == 0 then 0 else 1)

@[inline] def bits (size : Size) : Except SizeError UInt64 :=
  if size.bytes > UInt64.ofNat (18446744073709551615 / 8) then
    .error (.bitCountOverflow size.bytes)
  else
    .ok (size.bytes * 8)

@[inline] def bitsNat (size : Size) : Except SizeError Nat := do
  return (← bits size).toNat

@[inline] def bytesNat (size : Size) : Nat := size.bytes.toNat

@[inline] def add (left right : Size) : Except SizeError Size :=
  let result := left.bytes + right.bytes
  if result < left.bytes then
    .error (.u64Overflow "add" left.bytes right.bytes)
  else
    .ok (ofBytes result)

@[inline] def sub (left right : Size) : Except SizeError Size :=
  if left.bytes < right.bytes then
    .error (.negativeSubtraction left.bytes right.bytes)
  else
    .ok (ofBytes (left.bytes - right.bytes))

@[inline] def mul (size : Size) (count : UInt64) : Except SizeError Size :=
  let result := size.bytes * count
  if count != 0 && result / count != size.bytes then
    .error (.u64Overflow "mul" size.bytes count)
  else
    .ok (ofBytes result)

/-! Checked target-layout addition. This mirrors the upstream exclusive bound:
the resulting byte count must be strictly less than `obj_size_bound()`. -/
@[inline] def checkedAdd {α : Type} [HasDataLayout α]
    (size offset : Size) (cx : α) : Option Size := Id.run do
  let result := size.bytes + offset.bytes
  if result < size.bytes then return none
  if result < (HasDataLayout.dataLayout cx).objSizeBound then
    return some (ofBytes result)
  return none

@[inline] def checkedMul {α : Type} [HasDataLayout α]
    (size : Size) (count : UInt64) (cx : α) : Option Size := Id.run do
  let result := size.bytes * count
  if count != 0 && result / count != size.bytes then return none
  if result < (HasDataLayout.dataLayout cx).objSizeBound then
    return some (ofBytes result)
  return none

private def integerWidth (size : Size) : Except SizeError Nat := do
  let bitCount ← bits size
  if bitCount > 128 then
    throw (.integerWidthTooLarge bitCount)
  return bitCount.toNat

/-! Truncate a `u128` value to the low `Size.bits` bits. The error case
corresponds to the upstream primitive's overflowing `bits()` or shift. -/
@[inline] def truncate (size : Size) (value : U128) : Except SizeError U128 := do
  let width ← integerWidth size
  if width == 0 then return 0
  let low := BitVec.extractLsb (width - 1) 0 value
  return BitVec.zeroExtend 128 low

/-! Truncate to `Size.bits` and interpret the resulting bits as a signed
two's-complement `i128`. -/
@[inline] def signExtend (size : Size) (value : U128) : Except SizeError Int := do
  let width ← integerWidth size
  if width == 0 then return 0
  let low := BitVec.extractLsb (width - 1) 0 value
  return (BitVec.signExtend 128 low).toInt

@[inline] def unsignedIntMax (size : Size) : Except SizeError U128 := do
  let width ← integerWidth size
  if width == 0 then throw .zeroWidthUnsignedBound
  return BitVec.ofNat 128 ((2 ^ width) - 1)

@[inline] def signedIntMin (size : Size) : Except SizeError Int := do
  let width ← integerWidth size
  if width == 0 then throw .zeroWidthSignedBound
  return -(Int.ofNat (2 ^ (width - 1)))

@[inline] def signedIntMax (size : Size) : Except SizeError Int := do
  let width ← integerWidth size
  if width == 0 then throw .zeroWidthSignedBound
  return Int.ofNat ((2 ^ (width - 1)) - 1)

end Size

end Miri.ABI
