import Miri.Interpreter.IntrinsicX86.Float
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

inductive Shift where
  | left | logicalRight | arithmeticRight
  deriving DecidableEq

def shiftScalar [PointerProvenance P] (value : Memory.Scalar P) (size : Size) (amount : Nat) (which : Shift) : M S (Memory.Scalar P) := do
  match which with
  | .left =>
    let value ← scalarResult (value.toUInt size)
    let value := if amount >= 128 then (0 : U128) else value <<< amount
    let result ← sizeResult (size.truncate value)
    scalarResult (Memory.Scalar.fromUInt result size)
  | .logicalRight =>
    let value ← scalarResult (value.toUInt size)
    scalarResult (Memory.Scalar.fromUInt (if amount >= 128 then 0 else value >>> amount) size)
  | .arithmeticRight =>
    let value ← scalarResult (value.toInt size)
    fromInt (value / Int.ofNat (2^(min amount 127))) size

def extractFirstU64 [PointerProvenance P] (h : Hooks P S C V) (choice : C) (source : OpTy P) : M S UInt64 := do
  let integer ← h.integerLayout choice 64 false
  let array ← h.arrayLayout choice integer.ty 2
  let source ← h.transmuteRead choice source array
  scalarResult ((← readScalarLane h choice source 0).toUInt64)

def shiftVector [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right : OpTy P) (dest : V) (which : Shift) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let left ← readScalarLane h choice left i
    let right ← readScalarLane h choice right i
    let dest ← h.architecture.simd.indexWrite choice dest i
    let size := (h.architecture.simd.placeLayout dest).layout.size
    let amount ← scalarResult (right.toUInt size)
    write h choice (← shiftScalar left size amount.toNat which) dest

def shiftByScalar [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right : OpTy P) (dest : V) (which : Shift) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (dest,n) ← projectWrite h choice dest
  same n ln
  let amount ← extractFirstU64 h choice right
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let value ← readScalarLane h choice left i
    let dest ← h.architecture.simd.indexWrite choice dest i
    write h choice (← shiftScalar value (h.architecture.simd.placeLayout dest).layout.size amount.toNat which) dest

def wideBinary [PointerProvenance P] (h : Hooks P S C V) (choice : C) (average : Bool)
    (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let left ← readLane h choice left i
    let right ← readLane h choice right i
    let dest ← h.architecture.simd.indexWrite choice dest i
    let layout := h.architecture.simd.placeLayout dest
    let wide ← h.twiceWideLayout choice left.layout.ty
    let left ← castInt h choice left wide
    let right ← castInt h choice right wide
    let value ← ScalarOps.binary h.architecture.simd.scalarOps choice (if average then .Add else .Mul) left right
    let value ← if average then do
      let value ← ScalarOps.binary h.architecture.simd.scalarOps choice .Add value (← makeImm 1 wide)
      ScalarOps.binary h.architecture.simd.scalarOps choice .Div value (← makeImm 2 wide)
      else do
        let bits ← sizeResult layout.layout.size.bits
        ScalarOps.binary h.architecture.simd.scalarOps choice .Shr value (← makeImm (Int.ofNat bits.toNat) wide)
    let value ← castInt h choice value layout
    h.architecture.simd.writeImmediate choice value.imm dest

def multiplyAdd [PointerProvenance P] (h : Hooks P S C V) (choice : C) (bytes : Bool)
    (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same ln rn
  same (← checkedIndex (n.toNat*2)) ln
  let operandSize := Size.ofBytes (if bytes then 1 else 2)
  for i in [:n.toNat] do
    let first ← checkedIndex (i*2)
    let l1 ← readScalarLane h choice left first
    let l1 ← if bytes then do pure (Int.ofNat (← scalarResult (l1.toUInt operandSize)).toNat) else scalarResult (l1.toInt operandSize)
    let r1 ← scalarResult ((← readScalarLane h choice right first).toInt operandSize)
    let second ← checkedIndex (first.toNat+1)
    let l2 ← readScalarLane h choice left second
    let l2 ← if bytes then do pure (Int.ofNat (← scalarResult (l2.toUInt operandSize)).toNat) else scalarResult (l2.toInt operandSize)
    let r2 ← scalarResult ((← readScalarLane h choice right second).toInt operandSize)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let result := l1*r1+l2*r2
    let value ← if bytes then fromInt (max (-32768) (min 32767 result)) (Size.ofBytes 2)
      else truncInt result (Size.ofBytes 4)
    write h choice value dest

def multiplyRound [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let left ← scalarResult ((← readScalarLane h choice left i).toInt16)
    let right ← scalarResult ((← readScalarLane h choice right i).toInt16)
    let dest ← h.architecture.simd.indexWrite choice dest i
    write h choice (← truncInt (((left.toInt*right.toInt)/2^14+1)/2) (Size.ofBytes 2)) dest

def signVector [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let dest ← h.architecture.simd.indexWrite choice dest i
    let left ← readLane h choice left i
    let layout := h.architecture.simd.placeLayout dest
    let right ← scalarResult ((← readScalarLane h choice right i).toInt layout.layout.size)
    let sign := if right < 0 then -1 else if right == 0 then 0 else 1
    let result ← ScalarOps.binary h.architecture.simd.scalarOps choice .Mul left (← makeImm sign layout)
    h.architecture.simd.writeImmediate choice result.imm dest

def shuffleBytes [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  for i in [:n.toNat] do
    let control ← scalarResult ((← readScalarLane h choice right (UInt64.ofNat i)).toUInt8)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let value ← if control &&& 128 == 0 then
      readScalarLane h choice left (← checkedIndex (i/16*16+control.toNat%16))
      else pure (.fromScalarInt (.ofUInt8 0))
    write h choice value dest

def permute [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left indices : OpTy P) (right : Option (OpTy P)) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (indices,inum) ← projectRead h choice indices
  let right ← match right with | none => pure none | some right => pure (some (← projectRead h choice right))
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n inum
  if let some (_,rn) := right then same n rn
  unless n.toNat.isPowerOfTwo do invalid "x86 permutation length must be power of two"
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let dest ← h.architecture.simd.indexWrite choice dest i
    let index ← h.architecture.simd.indexRead choice indices i
    let bits ← scalarResult ((← read h choice index).toUInt index.layout.layout.size)
    let source := match right with | none => left | some (right,_) => if bits.toNat &&& n.toNat == 0 then left else right
    let source ← h.architecture.simd.indexRead choice source (UInt64.ofNat (bits.toNat &&& (n.toNat-1)))
    h.architecture.simd.copyOp choice source dest

def testBits [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (source mask : OpTy P) (high : Bool) : M S (Bool × Bool) := do
  unless source.layout == mask.layout do invalid "x86 bit test layout mismatch"
  let (source,sn) ← projectRead h choice source
  let (mask,mn) ← projectRead h choice mask
  same sn mn
  let shift ← if high then do
    let layout ← h.architecture.simd.fieldLayout choice source.layout 0
    let bits ← sizeResult layout.layout.size.bits
    if bits == 0 then invalid "x86 high bit strict subtraction"
    pure (bits.toNat-1)
    else pure 0
  let mut direct := true
  let mut negated := true
  for i in [:sn.toNat] do
    let i := UInt64.ofNat i
    let op ← h.architecture.simd.indexRead choice source i
    let mask ← h.architecture.simd.indexRead choice mask i
    let op ← scalarResult ((← read h choice op).toUInt op.layout.layout.size)
    let mask ← scalarResult ((← read h choice mask).toUInt mask.layout.layout.size)
    direct := direct && ((op &&& mask) >>> shift) == 0
    negated := negated && (if high then ((~~~op &&& mask) >>> shift) == 0 else (op &&& mask) == mask)
  pure (direct,negated)

end Miri.Interpreter.IntrinsicX86
