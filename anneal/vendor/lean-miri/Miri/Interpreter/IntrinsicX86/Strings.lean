import Miri.Interpreter.IntrinsicX86.Chunks
namespace Miri.Interpreter.IntrinsicX86
open Miri.ABI Miri.Memory Miri.MIR

def stringDefaultLength (imm : UInt8) : Nat := if imm &&& 1 != 0 then 8 else 16

def stringArray (h : Hooks P S C V) (choice : C) (imm : UInt8) : M S (TyAndLayout TyId) := do
  let integer ← h.integerLayout choice (if imm &&& 1 != 0 then 16 else 8) false
  h.arrayLayout choice integer.ty (UInt64.ofNat (stringDefaultLength imm))

def implicitLength [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (source : OpTy P) (imm : UInt8) : M S (Option Nat) := do
  let element ← h.architecture.simd.fieldLayout choice source.layout 0
  let zero ← makeImm 0 element
  let mut found := none
  for i in [:stringDefaultLength imm] do
    if found.isNone then
      let ch ← readLane h choice source (UInt64.ofNat i)
      let equal ← ScalarOps.binary h.architecture.simd.scalarOps choice .Eq ch zero
      if ← scalarResult ((← scalar equal).toBool) then found := some i
  pure found

def deconstructStrings [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (full name : String) (args : Array (OpTy P)) : M S (OpTy P × OpTy P × Option (Nat × Nat) × UInt8) := do
  let explicit := name.startsWith "pcmpe"
  unless explicit || name.startsWith "pcmpi" do invalid "string comparison name assertion"
  signature h choice full args (if explicit then 5 else 3)
  let imm ← scalarResult ((← read h choice (← arg args (if explicit then 4 else 2))).toUInt8)
  let lengths ← if explicit then do
    let a ← scalarResult ((← read h choice (← arg args 1)).toUInt32)
    let b ← scalarResult ((← read h choice (← arg args 3)).toUInt32)
    pure (some (min a.toNat (stringDefaultLength imm), min b.toNat (stringDefaultLength imm)))
    else pure none
  let layout ← stringArray h choice imm
  let a ← h.transmuteRead choice (← arg args 0) layout
  let b ← h.transmuteRead choice (← arg args (if explicit then 2 else 1)) layout
  pure (a,b,lengths,imm)

def compareStrings [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (a b : OpTy P) (lengths : Option (Nat × Nat)) (imm : UInt8) : M S Nat := do
  let defaultLen := stringDefaultLength imm
  let (an,bn) ← match lengths with
    | some pair => pure pair
    | none =>
      let a ← implicitLength h choice a imm
      let b ← implicitLength h choice b imm
      pure (a.getD defaultLen,b.getD defaultLen)
  let compare := fun op a b => do
    let compared ← ScalarOps.binary h.architecture.simd.scalarOps choice op a b
    scalarResult ((← scalar compared).toBool)
  let mut result := 0
  match (imm.toNat >>> 2) &&& 3 with
  | 0 =>
    for i in [:bn] do
      let ch2 ← readLane h choice b (UInt64.ofNat i)
      let mut found := false
      for j in [:an] do
        if !found then
          let ch1 ← readLane h choice a (UInt64.ofNat j)
          if ← compare .Eq ch1 ch2 then
            result := result ||| (1 <<< i)
            found := true
  | 1 =>
    let size := Size.ofBytes (if imm &&& 1 != 0 then 2 else 1)
    let getCh := fun value => if imm &&& 2 != 0 then scalarResult (value.toInt size)
      else do pure (Int.ofNat (← scalarResult (value.toUInt size)).toNat)
    for i in [:bn] do
      for j in [:an/2] do
        let ch2 ← getCh (← readScalarLane h choice b (UInt64.ofNat i))
        let lo ← getCh (← readScalarLane h choice a (UInt64.ofNat (j*2)))
        let hi ← getCh (← readScalarLane h choice a (UInt64.ofNat (j*2+1)))
        if lo <= ch2 && ch2 <= hi then result := result ||| (1 <<< i)
  | 2 =>
    result := (2^defaultLen-1) ^^^ (2^(max an bn)-1)
    for i in [:min an bn] do
      let ch1 ← readLane h choice a (UInt64.ofNat i)
      let ch2 ← readLane h choice b (UInt64.ofNat i)
      if ← compare .Eq ch1 ch2 then result := result ||| (1 <<< i)
  | _ =>
    if an == 0 then result := 2^defaultLen-1
    else if an <= bn then
      for i in [:bn] do
        if an <= bn-i then
          result := result ||| (1 <<< i)
          let mut stopped := false
          for j in [:an] do
            if !stopped then
              let k := i+j
              if k >= defaultLen then stopped := true
              else
                let ch1 ← readLane h choice a (UInt64.ofNat j)
                let ch2 ← readLane h choice b (UInt64.ofNat k)
                if ← compare .Ne ch1 ch2 then
                  result := result - (result &&& (1 <<< i))
                  stopped := true
  match (imm.toNat >>> 4) &&& 3 with
  | 3 => result := result ^^^ (2^an-1)
  | 1 => result := result ^^^ (2^defaultLen-1)
  | _ => pure ()
  pure result

private def writeI32 (h : Hooks P S C V) (choice : C) (value : Nat) (dest : V) : M S Unit :=
  write h choice (.fromScalarInt (.ofUInt32 (UInt32.ofNat value))) dest

def stringDispatch [PointerProvenance P] (h : Hooks P S C V) (choice : C)
    (full name : String) (args : Array (OpTy P)) (dest : V) : M S Bool := do
  if name == "pcmpistriz128" || name == "pcmpistris128" then
    signature h choice full args 3
    let imm ← scalarResult ((← read h choice (← arg args 2)).toUInt8)
    let source ← arg args (if name == "pcmpistris128" then 0 else 1)
    let layout ← stringArray h choice imm
    let source ← h.transmuteRead choice source layout
    let length ← implicitLength h choice source imm
    writeI32 h choice (if length.isSome then 1 else 0) dest
  else if name == "pcmpestriz128" || name == "pcmpestris128" then
    signature h choice full args 5
    let length ← scalarResult ((← read h choice (← arg args (if name == "pcmpestris128" then 1 else 3))).toInt32)
    let imm ← scalarResult ((← read h choice (← arg args 4)).toUInt8)
    writeI32 h choice (if length.toInt < Int.ofNat (stringDefaultLength imm) then 1 else 0) dest
  else if ["pcmpistrm128","pcmpestrm128","pcmpistria128","pcmpestria128","pcmpistri128","pcmpestri128",
      "pcmpistrio128","pcmpestrio128","pcmpistric128","pcmpestric128"].contains name then
    let (a,b,lengths,imm) ← deconstructStrings h choice full name args
    let mask ← compareStrings h choice a b lengths imm
    if name == "pcmpistrm128" || name == "pcmpestrm128" then
      if imm &&& 64 != 0 then
        let layout ← stringArray h choice imm
        let size := Size.ofBytes (if imm &&& 1 != 0 then 2 else 1)
        let dest ← h.transmuteWrite choice dest layout
        for i in [:stringDefaultLength imm] do
          let value ← fromUInt (if mask &&& (1 <<< i) != 0 then 2^(size.bytes.toNat*8)-1 else 0) size
          write h choice value (← h.architecture.simd.indexWrite choice dest (UInt64.ofNat i))
      else
        let layout ← h.integerLayout choice 128 true
        let dest ← h.transmuteWrite choice dest layout
        write h choice (← fromInt (Int.ofNat mask) (Size.ofBytes 16)) dest
    else if name == "pcmpistria128" || name == "pcmpestria128" then
      let yes ← if mask != 0 then pure false else do
        match lengths with
        | some (_,n) => pure (n >= stringDefaultLength imm)
        | none => pure (← implicitLength h choice a imm).isSome
      writeI32 h choice (if yes then 1 else 0) dest
    else if name == "pcmpistri128" || name == "pcmpestri128" then
      let index := if mask == 0 then stringDefaultLength imm else if imm &&& 64 != 0 then
          min mask.log2 (stringDefaultLength imm)
        else min (((List.range 32).find? fun i => mask &&& (1 <<< i) != 0).getD 32) (stringDefaultLength imm)
      writeI32 h choice index dest
    else if name == "pcmpistrio128" || name == "pcmpestrio128" then writeI32 h choice (mask &&& 1) dest
    else writeI32 h choice (if mask != 0 then 1 else 0) dest
  else return false
  return true

end Miri.Interpreter.IntrinsicX86
