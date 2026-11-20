import Miri.Interpreter.IntrinsicX86.Integer
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

def pack [PointerProvenance P] (h : Hooks P S C V) (choice : C) (inputBits : Nat) (signed : Bool)
    (left right : OpTy P) (dest : V) : M S Unit := do
  unless left.layout == right.layout do invalid "x86 pack input layouts differ"
  unless left.layout.layout.size == (h.architecture.simd.placeLayout dest).layout.size do invalid "x86 pack sizes differ"
  let (chunks,items,left) ← splitRead h choice left
  let (_,_,right) ← splitRead h choice right
  let (_,outputItems,dest) ← splitWrite h choice dest
  same outputItems (← checkedIndex (items.toNat*2))
  let inSize := Size.fromBits (UInt64.ofNat inputBits)
  let outSize := Size.fromBits (UInt64.ofNat (inputBits/2))
  let lo : Int := if signed then -(2^(inputBits/2-1) : Int) else 0
  let hi : Int := if signed then 2^(inputBits/2-1)-1 else 2^(inputBits/2)-1
  for i in [:chunks.toNat] do
    let i := UInt64.ofNat i
    let left ← h.architecture.simd.indexRead choice left i
    let right ← h.architecture.simd.indexRead choice right i
    let dest ← h.architecture.simd.indexWrite choice dest i
    for j in [:items.toNat] do
      let left ← readScalarLane h choice left (UInt64.ofNat j)
      let right ← readScalarLane h choice right (UInt64.ofNat j)
      let leftDest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat j)
      let rightDest ← h.architecture.simd.indexWrite choice dest (← checkedIndex (j+items.toNat))
      let left ← scalarResult (left.toInt inSize)
      let right ← scalarResult (right.toInt inSize)
      let left ← fromInt (max lo (min hi left)) outSize
      let right ← fromInt (max lo (min hi right)) outSize
      write h choice left leftDest
      write h choice right rightDest

def sadBytes [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same ln rn
  same ln left.layout.layout.size.bytes
  same n (ln/8)
  for i in [:n.toNat] do
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let mut sum := 0
    for j in [:8] do
      let index ← checkedIndex (i*8+j)
      let left ← scalarResult ((← readScalarLane h choice left index).toUInt8)
      let right ← scalarResult ((← readScalarLane h choice right index).toUInt8)
      sum := sum + (if left < right then right.toNat-left.toNat else left.toNat-right.toNat)
      if sum >= 2^16 then invalid "x86 SAD strict u16 overflow"
    write h choice (← fromUInt sum (Size.ofBytes 8)) dest

def multipleSadBytes [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right imm : OpTy P) (dest : V) : M S Unit := do
  unless left.layout == right.layout do invalid "x86 MPSAD input layouts differ"
  unless left.layout.layout.size == (h.architecture.simd.placeLayout dest).layout.size do invalid "x86 MPSAD sizes differ"
  let (chunks,items,left) ← splitRead h choice left
  if chunks > 2 then invalid "x86 MPSAD chunks > 2"
  let (_,_,right) ← splitRead h choice right
  let (_,outputItems,dest) ← splitWrite h choice dest
  same items (← checkedIndex (outputItems.toNat*2))
  let imm ← scalarResult ((← read h choice imm).toUInt imm.layout.layout.size)
  for i in [:chunks.toNat] do
    let left ← h.architecture.simd.indexRead choice left (UInt64.ofNat i)
    let right ← h.architecture.simd.indexRead choice right (UInt64.ofNat i)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let laneImm := imm.toNat >>> (i*3)
    let leftBase := ((laneImm >>> 2) &&& 1)*4
    let rightBase := (laneImm &&& 3)*4
    for j in [:outputItems.toNat] do
      let mut sum := 0
      for k in [:4] do
        let left ← scalarResult ((← readScalarLane h choice left (← checkedIndex (leftBase+j+k))).toUInt8)
        let right ← scalarResult ((← readScalarLane h choice right (← checkedIndex (rightBase+k))).toUInt8)
        sum := sum + (if left < right then right.toNat-left.toNat else left.toNat-right.toNat)
        if sum >= 2^16 then invalid "x86 MPSAD strict u16 overflow"
      write h choice (← fromUInt sum (Size.ofBytes 2)) (← h.architecture.simd.indexWrite choice dest (UInt64.ofNat j))

def dotProduct [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right imm : OpTy P) (dest : V) : M S Unit := do
  unless left.layout == h.architecture.simd.placeLayout dest do invalid "dot input/output layouts differ"
  unless right.layout == h.architecture.simd.placeLayout dest do invalid "dot input/output layouts differ"
  let (chunks,items,left) ← splitRead h choice left
  let (_,_,right) ← splitRead h choice right
  let (_,_,dest) ← splitWrite h choice dest
  let inner ← h.architecture.simd.fieldLayout choice left.layout 0
  let element ← h.architecture.simd.fieldLayout choice inner 0
  if items > 4 then invalid "dot chunk has more than four elements"
  let imm ← scalarResult ((← read h choice imm).toUInt imm.layout.layout.size)
  for i in [:chunks.toNat] do
    let left ← h.architecture.simd.indexRead choice left (UInt64.ofNat i)
    let right ← h.architecture.simd.indexRead choice right (UInt64.ofNat i)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let mut sum ← makeImm 0 element
    for j in [:items.toNat] do
      if imm.getLsbD (j+4) then
        let left ← readLane h choice left (UInt64.ofNat j)
        let right ← readLane h choice right (UInt64.ofNat j)
        let product ← ScalarOps.binary h.architecture.simd.scalarOps choice .Mul left right
        sum ← ScalarOps.binary h.architecture.simd.scalarOps choice .Add sum product
    for j in [:items.toNat] do
      let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat j)
      if imm.getLsbD j then h.architecture.simd.writeImmediate choice sum.imm dest
      else write h choice (← fromInt 0 element.layout.size) dest

def carry [PointerProvenance P] (h : Hooks P S C V) (choice : C) (input a b : OpTy P)
    (op : BinOp) : M S (RvalueImmTy P × Memory.Scalar P) := do
  unless op == .AddWithOverflow || op == .SubWithOverflow do invalid "carry operation assertion"
  let carry ← scalarResult ((← read h choice input).toUInt8)
  let a ← h.architecture.simd.readImmediate choice a
  let b ← h.architecture.simd.readImmediate choice b
  let layout := a.layout
  let first ← ScalarOps.binary h.architecture.simd.scalarOps choice op a b
  let (value,overflow1) ← liftResult (first.imm.toScalarPair.mapError ScalarOps.immediateError)
  let sumLayout ← h.architecture.simd.fieldLayout choice first.layout 0
  let _ ← h.architecture.simd.fieldLayout choice first.layout 1
  let second ← ScalarOps.binary h.architecture.simd.scalarOps choice op ⟨.scalar value,sumLayout⟩ (← makeImm (if carry != 0 then 1 else 0) layout)
  let (value,overflow2) ← liftResult (second.imm.toScalarPair.mapError ScalarOps.immediateError)
  let sumLayout ← h.architecture.simd.fieldLayout choice second.layout 0
  let _ ← h.architecture.simd.fieldLayout choice second.layout 1
  let o1 ← scalarResult overflow1.toBool
  let o2 ← scalarResult overflow2.toBool
  pure (⟨.scalar value,sumLayout⟩,.fromScalarInt (.ofUInt8 (if o1 || o2 then 1 else 0)))

end Miri.Interpreter.IntrinsicX86
