import Miri.Interpreter.IntrinsicX86.Crypto
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

def bmi [PointerProvenance P] (h : Hooks P S C V) (choice : C) (full name : String)
    (args : Array (OpTy P)) (dest : V) : M S Bool := do
  let wide := name.endsWith "64"
  let suffix := if wide then ".64" else ".32"
  let name := if name.endsWith suffix then (name.dropEnd 3).toString else ""
  feature h choice full (if name == "bextr" then "bmi1" else "bmi2")
  if wide && !h.x86_64 then return false
  signature h choice full args 2
  let a ← read h choice (← arg args 0)
  let b ← read h choice (← arg args 1)
  let size := Size.ofBytes (if wide then 8 else 4)
  let a ← scalarResult (a.toUInt size)
  let b ← scalarResult (b.toUInt size)
  let a := a.toNat
  let b := b.toNat
  let result ← match name with
    | "bextr" =>
      let start := b &&& 255
      let len := (b >>> 8) &&& 255
      let shifted := if start >= 64 then 0 else a >>> start
      pure (if len >= 64 then shifted else shifted &&& (2^len-1))
    | "bzhi" => let index := b &&& 255; pure (if index >= 64 then a else a &&& (2^index-1))
    | "pext" =>
      let mut index := 0
      let mut result := 0
      for bit in [:64] do
        if b &&& (1 <<< bit) != 0 then
          if a &&& (1 <<< bit) != 0 then result := result ||| (1 <<< index)
          index := index+1
      pure result
    | "pdep" =>
      let mut index := 0
      let mut result := 0
      for bit in [:64] do
        if b &&& (1 <<< bit) != 0 then
          if a &&& (1 <<< index) != 0 then result := result ||| (1 <<< bit)
          index := index+1
      pure result
    | _ => return false
  if !wide && result >= 2^32 then invalid "BMI result u32 conversion overflow"
  write h choice (← fromUInt result size) dest
  return true

def gather [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (source slice offsets mask scale : OpTy P) (dest : V) : M S Unit := do
  unless source.layout == h.architecture.simd.placeLayout dest do invalid "gather source/destination layout mismatch"
  let (source,_) ← projectRead h choice source
  let (offsets,on) ← projectRead h choice offsets
  let (mask,mn) ← projectRead h choice mask
  let (dest,n) ← projectWrite h choice dest
  let actual := min n on
  same n mn
  let maskLayout ← h.architecture.simd.fieldLayout choice mask.layout 0
  let bits ← sizeResult maskLayout.layout.size.bits
  if bits == 0 then invalid "gather mask high-bit subtraction"
  let scale ← scalarResult ((← read h choice scale).toInt8)
  unless [1,2,4,8].contains scale.toInt do invalid "invalid gather scale"
  let pointer ← scalarResult ((← read h choice slice).toPointer h.architecture.simd.target)
  for i in [:actual.toNat] do
    let i := UInt64.ofNat i
    let mask ← h.architecture.simd.indexRead choice mask i
    let dest ← h.architecture.simd.indexWrite choice dest i
    let value ← scalarResult ((← read h choice mask).toUInt maskLayout.layout.size)
    if value >>> (bits.toNat-1) != 0 then
      let offset ← h.architecture.simd.indexRead choice offsets i
      let offset ← scalarResult ((← read h choice offset).toInt offset.layout.layout.size)
      let product := offset*scale.toInt
      unless -(2^63 : Int) <= offset && offset < 2^63 do invalid "gather offset does not fit i64"
      unless -(2^63 : Int) <= product && product < 2^63 do invalid "gather offset scaling overflow"
      let ptr ← liftResult ((pointer.wrappingSignedOffset (Int64.ofInt product)
        ⟨Size.fromBits h.architecture.simd.target.pointerWidth.bits⟩).mapError fun e => .invalidProgram s!"{reprStr e}")
      let destPtr ← liftResult (h.architecture.simd.placePointer dest)
      h.memCopy choice ptr destPtr (h.architecture.simd.placeLayout dest).layout.size true
    else h.architecture.simd.copyOp choice (← h.architecture.simd.indexRead choice source i) dest
  for i in [actual.toNat:n.toNat] do
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    write h choice (← fromInt 0 (h.architecture.simd.placeLayout dest).layout.size) dest

def ternary [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (a b c imm : OpTy P) (dest : V) : M S Unit := do
  let layout := h.architecture.simd.placeLayout dest
  unless layout == a.layout do invalid "ternlog layout mismatch a"
  unless layout == b.layout do invalid "ternlog layout mismatch b"
  unless layout == c.layout do invalid "ternlog layout mismatch c"
  let (a,_) ← projectRead h choice a
  let (b,_) ← projectRead h choice b
  let (c,_) ← projectRead h choice c
  let (dest,n) ← projectWrite h choice dest
  let imm ← scalarResult ((← read h choice imm).toUInt32)
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let a ← h.architecture.simd.indexRead choice a i
    let b ← h.architecture.simd.indexRead choice b i
    let c ← h.architecture.simd.indexRead choice c i
    let dest ← h.architecture.simd.indexWrite choice dest i
    let size := (h.architecture.simd.placeLayout dest).layout.size
    let a ← scalarResult ((← read h choice a).toBits size)
    let b ← scalarResult ((← read h choice b).toBits size)
    let c ← scalarResult ((← read h choice c).toBits size)
    let bits ← sizeResult size.bits
    let mut result := 0
    for bit in [:bits.toNat] do
      let index := ((a.toNat >>> bit) &&& 1)*4+((b.toNat >>> bit) &&& 1)*2+((c.toNat >>> bit) &&& 1)
      result := result ||| (((imm.toNat >>> index) &&& 1) <<< bit)
    write h choice (← fromUInt result size) dest

def dotBytes [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (source a b : OpTy P) (dest : V) : M S Unit := do
  let (source,sn) ← projectRead h choice source
  let (a,an) ← projectRead h choice a
  let (b,bn) ← projectRead h choice b
  let (dest,n) ← projectWrite h choice dest
  same sn n
  same an (← checkedIndex (n.toNat*4))
  same bn an
  for i in [:n.toNat] do
    let value ← scalarResult ((← readScalarLane h choice source (UInt64.ofNat i)).toInt32)
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    let mut sum : Int := 0
    for j in [:4] do
      let index ← checkedIndex (i*4+j)
      let a ← scalarResult ((← readScalarLane h choice a index).toUInt8)
      let b ← scalarResult ((← readScalarLane h choice b index).toInt8)
      sum := sum+Int.ofNat a.toNat*b.toInt
    write h choice (← truncInt (sum+value.toInt) (Size.ofBytes 4)) dest

def permuteFloat [PointerProvenance P] (h : Hooks P S C V) (choice : C) (double : Bool)
    (data control : OpTy P) (dest : V) : M S Unit := do
  let (data,dn) ← projectRead h choice data
  let (control,cn) ← projectRead h choice control
  let (dest,n) ← projectWrite h choice dest
  same n dn
  same n cn
  let chunk := if double then 2 else 4
  for i in [:n.toNat] do
    let control ← h.architecture.simd.indexRead choice control (UInt64.ofNat i)
    let control ← scalarResult ((← read h choice control).toUInt (Size.ofBytes (if double then 8 else 4)))
    let index := if double then (control.toNat >>> 1) &&& 1 else control.toNat &&& 3
    let src ← h.architecture.simd.indexRead choice data (← checkedIndex (i/chunk*chunk+index))
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    h.architecture.simd.copyOp choice src dest

def insertPs [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (left right imm : OpTy P) (dest : V) : M S Unit := do
  let (left,ln) ← projectRead h choice left
  let (right,rn) ← projectRead h choice right
  let (dest,n) ← projectWrite h choice dest
  same n ln
  same n rn
  if n > 4 then invalid "insertps length > 4"
  let imm ← scalarResult ((← read h choice imm).toUInt8)
  let source ← readLane h choice right (UInt64.ofNat ((imm.toNat >>> 6) &&& 3))
  for i in [:n.toNat] do
    let dest ← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i)
    if imm.toNat &&& (1 <<< i) != 0 then write h choice (.fromScalarInt (.ofUInt32 0)) dest
    else if i == ((imm.toNat >>> 4) &&& 3) then h.architecture.simd.writeImmediate choice source.imm dest
    else h.architecture.simd.copyOp choice (← h.architecture.simd.indexRead choice left (UInt64.ofNat i)) dest

def minPosition [PointerProvenance P] (h : Hooks P S C V) (choice : C) (source : OpTy P) (dest : V) : M S Unit := do
  let (source,sn) ← projectRead h choice source
  let (dest,n) ← projectWrite h choice dest
  let mut minimum : UInt16 := 65535
  let mut index := 0
  for i in [:sn.toNat] do
    let value ← scalarResult ((← readScalarLane h choice source (UInt64.ofNat i)).toUInt16)
    if value < minimum then minimum := value; index := i
  write h choice (.fromScalarInt (.ofUInt16 minimum)) (← h.architecture.simd.indexWrite choice dest 0)
  if index >= 2^16 then invalid "minimum position does not fit u16"
  write h choice (.fromScalarInt (.ofUInt16 (UInt16.ofNat index))) (← h.architecture.simd.indexWrite choice dest 1)
  for i in [2:n.toNat] do write h choice (.fromScalarInt (.ofUInt16 0)) (← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i))

end Miri.Interpreter.IntrinsicX86
