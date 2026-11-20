import Miri.Interpreter.IntrinsicCrypto

/-! Complete pinned AArch64 and LoongArch LLVM intrinsic dispatch. Canonical
SIMD projection and scalar operations retain type, provenance and memory effects. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR

structure ArchitectureHooks (P S C V : Type) where
  simd : IntrinsicSimdHooks P S C V
  /-- Compiler symbol-clash check from shims/sig.rs. Argument count is checked below. -/
  checkSignature : C → String → Nat → RvalueM S Unit
  expectFeature : C → String → String → RvalueM S Unit
  transmuteDestU128 : C → V → RvalueM S V

namespace IntrinsicArchitecture
open IntrinsicCrypto

private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def liftResult (value : Except StepError A) : RvalueM S A :=
  match value with | .ok value => pure value | .error error => throw error
private def scalarResult (value : Except ScalarError A) : RvalueM S A :=
  liftResult (value.mapError ScalarOps.scalarError)
private def arg (args : Array (OpTy P)) (i : Nat) : RvalueM S (OpTy P) :=
  match args[i]? with | some value => pure value | none => invalid "LLVM intrinsic argument missing"
private def signature (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (n : Nat) : RvalueM S Unit := do
  unless name.startsWith "llvm." do invalid "LLVM signature helper prefix assertion"
  h.checkSignature choice name n
  unless args.size == n do throw (.undefinedBehavior "incorrect number of arguments for LLVM intrinsic")
private def readScalar (h : ArchitectureHooks P S C V) (choice : C) (op : OpTy P) : RvalueM S (Memory.Scalar P) := do
  let value ← h.simd.readImmediate choice op
  liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
private def readLane (h : ArchitectureHooks P S C V) (choice : C) (op : OpTy P) (i : UInt64) : RvalueM S (RvalueImmTy P) := do
  h.simd.readImmediate choice (← h.simd.indexRead choice op i)
private def scalarLane (h : ArchitectureHooks P S C V) (choice : C) (op : OpTy P) (i : UInt64) : RvalueM S (Memory.Scalar P) := do
  readScalar h choice (← h.simd.indexRead choice op i)
private def arrayLength (layout : TyAndLayout TyId) : RvalueM S UInt64 :=
  match layout.layout.fields with | .Array _ n => pure n | _ => invalid "SIMD sole field is not array"
private def projectRead (h : ArchitectureHooks P S C V) (choice : C) (op : OpTy P) : RvalueM S (OpTy P × UInt64) := do
  unless ← h.simd.isSimd choice op.layout.ty do invalid "project_to_simd requires SIMD type"
  let array ← h.simd.fieldRead choice op 0
  return (array, ← arrayLength array.layout)
private def projectWrite (h : ArchitectureHooks P S C V) (choice : C) (dest : V) : RvalueM S (V × UInt64) := do
  unless ← h.simd.isSimd choice (h.simd.placeLayout dest).ty do invalid "project_to_simd requires SIMD type"
  let array ← h.simd.fieldWrite choice dest 0
  return (array, ← arrayLength (h.simd.placeLayout array))
private def writeScalar (h : ArchitectureHooks P S C V) (choice : C) (value : Memory.Scalar P) (dest : V) : RvalueM S Unit :=
  h.simd.writeImmediate choice (.scalar value) dest
private def same (a b : UInt64) : RvalueM S Unit :=
  unless a == b do invalid "architecture SIMD length mismatch"
private def checkedDouble (n : UInt64) : RvalueM S UInt64 :=
  if n.toNat*2 >= 2^64 then invalid "architecture SIMD index overflow" else pure (n*2)

private def readQuad [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (op : OpTy P) : RvalueM S (Quad UInt32) := do
  let a ← scalarResult ((← scalarLane h choice op 0).toUInt32)
  let b ← scalarResult ((← scalarLane h choice op 1).toUInt32)
  let c ← scalarResult ((← scalarLane h choice op 2).toUInt32)
  let d ← scalarResult ((← scalarLane h choice op 3).toUInt32)
  return ⟨a,b,c,d⟩
private def writeQuad (h : ArchitectureHooks P S C V) (choice : C) (dest : V) (value : Quad UInt32) : RvalueM S Unit := do
  for (i, value) in [(0,value.a), (1,value.b), (2,value.c), (3,value.d)] do
    let lane ← h.simd.indexWrite choice dest i
    writeScalar h choice (.fromScalarInt (.ofUInt32 value)) lane

private def crcParams (name : String) : Option (Nat × U128) :=
  match name with
  | "crc32b" | "crc.w.b.w" => some (8, 0x104C11DB7)
  | "crc32h" | "crc.w.h.w" => some (16, 0x104C11DB7)
  | "crc32w" | "crc.w.w.w" => some (32, 0x104C11DB7)
  | "crc32x" | "crc.w.d.w" => some (64, 0x104C11DB7)
  | "crc32cb" | "crcc.w.b.w" => some (8, 0x11EDC6F41)
  | "crc32ch" | "crcc.w.h.w" => some (16, 0x11EDC6F41)
  | "crc32cw" | "crcc.w.w.w" => some (32, 0x11EDC6F41)
  | "crc32cx" | "crcc.w.d.w" => some (64, 0x11EDC6F41)
  | _ => none

private def crc [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) (bits : Nat) (polynomial : U128)
    (loong : Bool) : RvalueM S Unit := do
  signature h choice name args 2
  let first ← readScalar h choice (← arg args 0)
  let second ← readScalar h choice (← arg args 1)
  let c ← scalarResult ((if loong then second else first).toUInt32)
  let dataScalar := if loong then first else second
  let data ← if bits == 64 then scalarResult dataScalar.toUInt64 else do
    let data ← scalarResult dataScalar.toUInt32
    pure (UInt64.ofNat (if loong then data.toNat % 2^bits else data.toNat))
  let result ← liftResult (IntrinsicCrypto.crc32 c data bits polynomial)
  writeScalar h choice (.fromScalarInt (.ofUInt32 result)) dest

/-- AArch64 pairwise SIMD operations, including all source shape checks before
lane reads and per-lane partial destination writes. -/
private def pairwise [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) (maximum : Bool) : RvalueM S Unit := do
  signature h choice name args 2
  let (left, ln) ← projectRead h choice (← arg args 0)
  let (right, rn) ← projectRead h choice (← arg args 1)
  let (dest, n) ← projectWrite h choice dest
  same ln rn
  same n ln
  if !maximum then
    unless left.layout == right.layout && left.layout == h.simd.placeLayout dest do invalid "addp SIMD layouts differ"
    unless n % 2 == 0 do invalid "addp requires even lane count"
  let half := n / 2
  for i in [:n.toNat] do
    if half == 0 then invalid "pairwise strict division by zero"
    let index := UInt64.ofNat i
    let source := if index < half then left else right
    let sourceIndex := if maximum then index % half else if index < half then index else index-half
    let first ← checkedDouble sourceIndex
    if first.toNat+1 >= 2^64 then invalid "pairwise source index overflow"
    let a ← readLane h choice source first
    let b ← readLane h choice source (first+1)
    let result ← if maximum then do
      let compared ← ScalarOps.binary h.simd.scalarOps choice .Gt a b
      let compared ← liftResult (compared.imm.toScalar.mapError ScalarOps.immediateError)
      let greater ← scalarResult compared.toBool
      pure (if greater then a else b)
      else ScalarOps.binary h.simd.scalarOps choice .Add a b
    let dest ← h.simd.indexWrite choice dest index
    h.simd.writeImmediate choice result.imm dest

private def widening [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Unit := do
  signature h choice name args 1
  let (source, sn) ← projectRead h choice (← arg args 0)
  let (dest, n) ← projectWrite h choice dest
  same sn (← checkedDouble n)
  let sourceElement ← h.simd.fieldLayout choice source.layout 0
  let destElement ← h.simd.fieldLayout choice (h.simd.placeLayout dest) 0
  let sourceSize := sourceElement.layout.size
  let destSize := destElement.layout.size
  same destSize.bytes (← checkedDouble sourceSize.bytes)
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    let sourceIndex ← checkedDouble index
    let a ← scalarLane h choice source sourceIndex
    let b ← scalarLane h choice source (sourceIndex+1)
    let a ← scalarResult (a.toUInt sourceSize)
    let b ← scalarResult (b.toUInt sourceSize)
    if a.toNat+b.toNat >= 2^128 then invalid "widening add strict u128 overflow"
    let value ← scalarResult (Memory.Scalar.fromUInt (BitVec.ofNat 128 (a.toNat+b.toNat)) destSize)
    writeScalar h choice value (← h.simd.indexWrite choice dest index)

private def doublingMultiply [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Unit := do
  signature h choice name args 2
  let (left, ln) ← projectRead h choice (← arg args 0)
  let (right, rn) ← projectRead h choice (← arg args 1)
  let (dest, n) ← projectWrite h choice dest
  same ln rn
  same ln n
  let element ← h.simd.fieldLayout choice (h.simd.placeLayout dest) 0
  let size := element.layout.size
  let bits ← liftResult (size.bits.mapError fun error => .invalidProgram s!"{reprStr error}")
  let minimum ← liftResult (size.signedIntMin.mapError fun error => .invalidProgram s!"{reprStr error}")
  let maximum ← liftResult (size.signedIntMax.mapError fun error => .invalidProgram s!"{reprStr error}")
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let a ← scalarResult ((← scalarLane h choice left i).toInt size)
    let b ← scalarResult ((← scalarLane h choice right i).toInt size)
    let product := a*b
    unless -(2^127 : Int) <= product && product < 2^127 do invalid "sqdmulh strict i128 multiplication overflow"
    let doubled := product*2
    unless -(2^127 : Int) <= doubled && doubled < 2^127 do invalid "sqdmulh strict i128 doubling overflow"
    let result := max minimum (min maximum (doubled / (Int.ofNat (2^bits.toNat))))
    let scalar ← scalarResult (Memory.Scalar.fromInt result size)
    writeScalar h choice scalar (← h.simd.indexWrite choice dest i)

private def tableLookup [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (full name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Unit := do
  let segments ← match name with
    | "neon.tbl1.v8i8" | "neon.tbl1.v16i8" => pure 1
    | "neon.tbl2.v8i8" | "neon.tbl2.v16i8" => pure 2
    | "neon.tbl3.v8i8" | "neon.tbl3.v16i8" => pure 3
    | "neon.tbl4.v8i8" | "neon.tbl4.v16i8" => pure 4
    | _ => invalid "unreachable AArch64 table intrinsic suffix"
  signature h choice full args (segments+1)
  let mut tables : Array (OpTy P × UInt64) := #[]
  for i in [:segments] do tables := tables.push (← projectRead h choice (← arg args i))
  for (_, n) in tables do same n 16
  let (indices, inum) ← projectRead h choice (← arg args segments)
  let (dest, n) ← projectWrite h choice dest
  same inum n
  for i in [:n.toNat] do
    let i := UInt64.ofNat i
    let index ← scalarResult ((← scalarLane h choice indices i).toUInt8)
    let value ← if index.toNat < segments*16 then do
      let some table := tables[index.toNat/16]? | invalid "table segment index assertion"
      scalarLane h choice table.1 (UInt64.ofNat (index.toNat%16))
      else pure (.fromScalarInt (.ofUInt8 0))
    writeScalar h choice value (← h.simd.indexWrite choice dest i)

private def sha [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (full name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Unit := do
  let binary := name == "crypto.sha256su0"
  signature h choice full args (if binary then 2 else 3)
  let (a, an) ← projectRead h choice (← arg args 0)
  let (b, bn) ← projectRead h choice (← arg args 1)
  let third ← if binary then pure none else pure (some (← projectRead h choice (← arg args 2)))
  let (dest, n) ← projectWrite h choice dest
  same an 4
  same bn 4
  if let some (_, cn) := third then same cn 4
  same n 4
  let a ← readQuad h choice a
  let b ← readQuad h choice b
  let result ← if binary then pure (shaSu0 a b) else do
    let some (c, _) := third | invalid "SHA third source missing"
    let c ← readQuad h choice c
    match name with
    | "crypto.sha256h" => pure (shaHash a b c).1
    | "crypto.sha256h2" => pure (shaHash b a c).2
    | "crypto.sha256su1" => pure (shaSu1 a b c)
    | _ => invalid "unreachable SHA operation"
  writeQuad h choice dest result

/-- Full inspected architecture dispatch; false is source NotSupported for
unrecognized names, while recognized malformed inputs retain explicit errors. -/
def aarch64 [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Bool := do
  unless name.startsWith "llvm.aarch64." do invalid "AArch64 intrinsic prefix assertion"
  let suffix := (name.drop 13).toString
  if suffix == "neon.umaxp.v16i8" then pairwise h choice name args dest true
  else if suffix.startsWith "neon.addp." then pairwise h choice name args dest false
  else if suffix.startsWith "neon.uaddlp." then widening h choice name args dest
  else if suffix.startsWith "neon.sqdmulh." then doublingMultiply h choice name args dest
  else if suffix.startsWith "neon.tbl" then tableLookup h choice name suffix args dest
  else if let some (bits, polynomial) := (if suffix.startsWith "crc32" then crcParams suffix else none) then
    h.expectFeature choice name "crc"
    crc h choice name args dest bits polynomial false
  else if suffix == "neon.pmull64" then
    h.expectFeature choice name "aes"
    signature h choice name args 2
    let left ← scalarResult ((← readScalar h choice (← arg args 0)).toUInt64)
    let right ← scalarResult ((← readScalar h choice (← arg args 1)).toUInt64)
    let dest ← h.transmuteDestU128 choice dest
    writeScalar h choice (.fromScalarInt (.ofUInt128 (carryless64 left right))) dest
  else if suffix == "crypto.sha256h" || suffix == "crypto.sha256h2" ||
      suffix == "crypto.sha256su0" || suffix == "crypto.sha256su1" then
    h.expectFeature choice name "sha2"
    sha h choice name suffix args dest
  else return false
  return true

def loongarch [PointerProvenance P] (h : ArchitectureHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) : RvalueM S Bool := do
  unless name.startsWith "llvm.loongarch." do invalid "LoongArch intrinsic prefix assertion"
  let suffix := (name.drop 15).toString
  unless h.simd.target.pointerWidth.bits == 64 do return false
  match (if suffix.startsWith "crc." || suffix.startsWith "crcc." then crcParams suffix else none) with
  | none => return false
  | some (bits, polynomial) =>
    crc h choice name args dest bits polynomial true
    return true

structure DispatchHooks (P S C V : Type) where
  architecture : ArchitectureHooks P S C V
  targetArch : String
  /-- Explicit remaining x86 source-port obligation; no arithmetic default. -/
  x86 : C → String → Array (OpTy P) → V → RvalueM S Bool
  unsupportedForeignItem : String → String → StepError

/-- Complete LLVM top-level staging around this ported architecture family.
Destination allocation precedes every dispatch guard, including unknown names. -/
def callLlvm [PointerProvenance P] (h : DispatchHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) (ret : Option BasicBlockId) : RvalueM S Unit := do
  let ops := h.architecture
  let dest ← ops.simd.forceAllocation choice dest
  let handled ← if name == "llvm.prefetch.p0" then do
    signature ops choice name args 4
    let pointer ← readScalar ops choice (← arg args 0)
    let _ ← scalarResult (pointer.toPointer ops.simd.target)
    let rw ← scalarResult ((← readScalar ops choice (← arg args 1)).toInt32)
    let locality ← scalarResult ((← readScalar ops choice (← arg args 2)).toInt32)
    let type ← scalarResult ((← readScalar ops choice (← arg args 3)).toInt32)
    if type == 1 then
      unless rw == 0 || rw == 1 do throw (.unsupported "invalid rw value passed to llvm.prefetch")
      unless 0 <= locality.toInt && locality.toInt <= 3 do throw (.unsupported "invalid loc value passed to llvm.prefetch")
    else throw (.unsupported "unsupported llvm.prefetch type argument")
    pure true
    else if name.startsWith "llvm.ctpop.v" && ops.simd.target.endian == .little then do
      signature ops choice name args 1
      let (source, sn) ← projectRead ops choice (← arg args 0)
      let (dest, dn) ← projectWrite ops choice dest
      same dn sn
      for i in [:dn.toNat] do
        let index := UInt64.ofNat i
        let value ← readLane ops choice source index
        let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
        let bits ← scalarResult (scalar.toUInt value.layout.layout.size)
        let count := (List.range 128).foldl (fun n i => n + if bits.getLsbD i then 1 else 0) 0
        let result ← scalarResult (Memory.Scalar.fromUInt (BitVec.ofNat 128 count) value.layout.layout.size)
        writeScalar ops choice result (← ops.simd.indexWrite choice dest index)
      pure true
    else if name.startsWith "llvm.x86." && (h.targetArch == "x86" || h.targetArch == "x86_64") &&
        ops.simd.target.endian == .little then h.x86 choice name args dest
    else if name.startsWith "llvm.aarch64." && h.targetArch == "aarch64" &&
        ops.simd.target.endian == .little then aarch64 ops choice name args dest
    else if name.startsWith "llvm.loongarch." && (h.targetArch == "loongarch32" || h.targetArch == "loongarch64") &&
        ops.simd.target.endian == .little then loongarch ops choice name args dest
    else pure false
  unless handled do throw (h.unsupportedForeignItem name h.targetArch)
  ops.simd.returnToBlock choice ret

end IntrinsicArchitecture
end Miri.Interpreter
