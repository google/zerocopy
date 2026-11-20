import Miri.ABI.Size

/-!
The power-of-two alignment primitives from `rustc_abi::Align`.

Alignments created from target data or byte counts are restricted to the
upstream maximum exponent 29. `maxAlignedFactor 0` deliberately preserves the
upstream exponent 64 sentinel; asking for its byte count is represented as an
explicit shift error, while `restrictForOffset` safely reduces it first.
-/

namespace Miri.ABI

inductive AlignError where
  | notPowerOfTwo (bytes : UInt64)
  | tooLarge (bytes : UInt64)
  | shiftOverflow (pow2 : Nat)
  | sizeOverflow (size : Size) (mask : UInt64)
  deriving Repr, DecidableEq

instance : ToString AlignError where
  toString
    | .notPowerOfTwo bytes => s!"{bytes} is not a power of 2"
    | .tooLarge bytes => s!"{bytes} is too large"
    | .shiftOverflow pow2 => s!"alignment exponent {pow2} does not fit in u64"
    | .sizeOverflow size mask =>
        s!"Size.alignTo: {size.bytes} + {mask} does not fit in u64"

structure Align where
  /- Same representation as rustc_abi: the exponent of the power of two. -/
  pow2 : Nat
  deriving DecidableEq, Repr

namespace Align

def ONE : Align := ⟨0⟩
def EIGHT : Align := ⟨3⟩
def MAX : Align := ⟨29⟩

private def countTrailingZerosAux (value : UInt64) : Nat → Nat
  | 0 => 0
  | remaining + 1 =>
      if value % 2 == 0 then
        1 + countTrailingZerosAux (value / 2) remaining
      else
        0

private def countTrailingZeros (value : UInt64) : Nat :=
  if value == 0 then 64 else countTrailingZerosAux value 64

@[inline] def fromBytes (bytes : UInt64) : Except AlignError Align := do
  if bytes == 0 then return ONE
  let power := countTrailingZeros bytes
  if UInt64.shiftLeft 1 (UInt64.ofNat power) != bytes then
    throw (.notPowerOfTwo bytes)
  if power > MAX.pow2 then
    throw (.tooLarge bytes)
  return ⟨power⟩

@[inline] def fromBits (bits : UInt64) : Except AlignError Align :=
  fromBytes (Size.fromBits bits).bytes

@[inline] def bytes (align : Align) : Except AlignError UInt64 :=
  if align.pow2 >= 64 then
    .error (.shiftOverflow align.pow2)
  else
    .ok (UInt64.shiftLeft 1 (UInt64.ofNat align.pow2))

@[inline] def bits (align : Align) : Except AlignError UInt64 := do
  return (← bytes align) * 8

@[inline] def bytesNat (align : Align) : Except AlignError Nat := do
  return (← bytes align).toNat

@[inline] def bitsNat (align : Align) : Except AlignError Nat := do
  return (← bits align).toNat

@[inline] def maxForTarget (layout : TargetDataLayout) : Align :=
  ⟨min (layout.pointerWidth.bits.toNat - 1) MAX.pow2⟩

@[inline] def maxAlignedFactor (size : Size) : Align :=
  ⟨countTrailingZeros size.bytes⟩

@[inline] def restrictForOffset (align : Align) (size : Size) : Align :=
  ⟨min align.pow2 (maxAlignedFactor size).pow2⟩

@[inline] def min (left right : Align) : Align := ⟨Nat.min left.pow2 right.pow2⟩

@[inline] def max (left right : Align) : Align := ⟨Nat.max left.pow2 right.pow2⟩

end Align

/-! ABI-mandated alignment wrapper used by target layout. -/
structure AbiAlign where
  abi : Align
  deriving DecidableEq, Repr

namespace AbiAlign

@[inline] def new (align : Align) : AbiAlign := ⟨align⟩

@[inline] def min (left right : AbiAlign) : AbiAlign :=
  ⟨Align.min left.abi right.abi⟩

@[inline] def max (left right : AbiAlign) : AbiAlign :=
  ⟨Align.max left.abi right.abi⟩

end AbiAlign

namespace Size

@[inline] def alignTo (size : Size) (align : Align) : Except AlignError Size := do
  let alignmentBytes ← Align.bytes align
  let mask := alignmentBytes - 1
  let sum := size.bytes + mask
  if sum < size.bytes then
    throw (.sizeOverflow size mask)
  return Size.ofBytes (UInt64.land sum (~~~mask))

@[inline] def isAligned (size : Size) (align : Align) : Except AlignError Bool := do
  let alignmentBytes ← Align.bytes align
  let mask := alignmentBytes - 1
  return UInt64.land size.bytes mask == 0

end Size

end Miri.ABI
