import Miri.Interpreter.ForeignItems
import Miri.Memory.Pointer

/-! Pinned portable C memory/string arms of shims/foreign_items.rs and the
read_c_str helper. Pointer checks are preserved even for zero-byte C accesses.
Concrete string scanning has an explicit resource budget, whose exhaustion is
Unknown; it is never treated as an empty string or a successful execution.
-/
namespace Miri.Interpreter.MemoryShims
open Miri.ABI Miri.Memory Miri.MIR
open ForeignItems (EmulateItemResult)
abbrev M := EStateM StepError

structure Operations (P S D MD B I : Type) where
  /-- ptr_get_alloc_id(...,0), with source dangling/provenance behavior. -/
  checkPointer : Pointer (Option P) → M S Unit
  readByte : Pointer (Option P) → M S UInt8
  readBytes : Pointer (Option P) → UInt64 → M S ByteArray
  offset : Pointer (Option P) → UInt64 → M S (Pointer (Option P))
  copy : Pointer (Option P) → Pointer (Option P) → UInt64 → Bool → M S Unit
  writeRepeatedByte : Pointer (Option P) → UInt8 → UInt64 → M S Unit
  writeI32 : Int32 → MD → M S Unit
  writeUsize : UInt64 → MD → M S Unit
  /-- Actual libc wchar_t (u16 on Windows), not the Lean host's wchar type. -/
  wcharLayout : M S (Size × Align)
  checkAlignment : Pointer (Option P) → Align → M S Unit
  readUnsigned : Pointer (Option P) → Size → M S U128


structure CoreHooks (P S D MD B I : Type) extends Operations P S D MD B I where
  foreign : ForeignItems.Core P S D MD (Pointer (Option P)) B I

structure Hooks (P S D MD B I : Type) extends Operations P S D MD B I where
  foreign : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I

def Hooks.core (h : Hooks P S D MD B I) : CoreHooks P S D MD B I :=
  {toOperations := h.toOperations,foreign := h.foreign.toCore}
instance : CoeOut (Hooks P S D MD B I) (CoreHooks P S D MD B I) := ⟨Hooks.core⟩

namespace Source
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "memory shim missing checked argument")

/-- Each character is read separately; a match prevents all later accesses. -/
def memchr (h : CoreHooks P S D MD B I) (pointer : Pointer (Option P))
    (count : UInt64) (reverse : Bool) (needle : UInt8) : M S (Option (UInt64 × Pointer (Option P))) := do
  for position in [:count.toNat] do
    let index := UInt64.ofNat (if reverse then count.toNat-1-position else position)
    let actual ← h.offset pointer index
    if (← h.readByte actual) == needle then return some (index,actual)
  return none

private def cStringLength (h : CoreHooks P S D MD B I) (pointer : Pointer (Option P)) :
    Nat → Nat → M S UInt64
  | 0,_ => throw (.resourceExhaustion "C string scan budget")
  | fuel+1,length => do
    if length ≥ 2^64 then throw (.invalidProgram "C string length overflow")
    let actual ← h.offset pointer (UInt64.ofNat length)
    if (← h.readByte actual) == 0 then return UInt64.ofNat length
    cStringLength h pointer fuel (length+1)

/-- Source read_c_str deliberately reads all bytes a second time after the
terminator scan, including a zero-length read for the empty string. -/
def readCString (h : CoreHooks P S D MD B I) (budget : Nat) (pointer : Pointer (Option P)) : M S ByteArray := do
  let length ← cStringLength h pointer budget 0
  let bytes ← h.readBytes pointer length
  unless bytes.size == length.toNat do throw (.invalidProgram "C string byte-read length mismatch")
  return bytes

private def wideLength (h : CoreHooks P S D MD B I) (size : Size)
    (pointer : Pointer (Option P)) : Nat → Nat → M S UInt64
  | 0,_ => throw (.resourceExhaustion "wide string scan budget")
  | fuel+1,length => do
    let value ← h.readUnsigned pointer size
    if value == 0 then
      if length < 2^64 then return UInt64.ofNat length
      else throw (.invalidProgram "wide string length overflow")
    if value.toNat ≥ 2^32 then throw (.invalidProgram "wchar_t conversion exceeds u32")
    let pointer ← h.offset pointer size.bytes
    wideLength h size pointer fuel (length+1)

def wcharLength (h : CoreHooks P S D MD B I) (budget : Nat) (pointer : Pointer (Option P)) : M S UInt64 := do
  let (size,alignment) ← h.wcharLayout
  if size == .ZERO then throw (.invalidProgram "read_c_str_with_char_size requires nonzero size")
  h.checkAlignment pointer alignment
  wideLength h size pointer budget 0

private def compareList : List UInt8 → List UInt8 → Int32
  | [],[] => 0
  | [],_::_ => -1
  | _::_,[] => 1
  | a::left,b::right => if a < b then -1 else if a > b then 1 else compareList left right

private def compareBytes (left right : ByteArray) : Int32 :=
  compareList left.data.toList right.data.toList

/-- All argument reads and mandatory pointer checks precede actual memory
operations in the source order. memset truncates C int to unsigned char. -/
def emulate (h : CoreHooks P S D MD B I) (budget : Nat) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option EmulateItemResult) := do
  let f := h.foreign
  let signature : Option ForeignItems.Signature :=
    if name == "memcmp" then some ⟨.C,#[.pointer,.pointer,.usize],.i32⟩
    else if name == "memchr" || name == "memrchr" || name == "memset" then some ⟨.C,#[.pointer,.i32,.usize],.pointer⟩
    else if name == "strlen" || name == "wcslen" then some ⟨.C,#[.pointer],.usize⟩
    else if name == "strnlen" then some ⟨.C,#[.pointer,.usize],.usize⟩
    else if name == "memcpy" then some ⟨.C,#[.pointer,.pointer,.usize],.pointer⟩
    else if name == "strcpy" then some ⟨.C,#[.pointer,.pointer],.pointer⟩
    else none
  let some signature := signature | return none
  if name == "memrchr" then
    unless #["linux","android","freebsd"].contains f.os do
      throw (.unsupported "memrchr unavailable on this target OS")
  let args ← ForeignItems.Core.checkSignature f name signature abi args
  let pointer ← f.readPointer (← arg args 0)
  if name == "memcmp" then
    let right ← f.readPointer (← arg args 1)
    let length ← f.readUsize (← arg args 2)
    h.checkPointer pointer
    h.checkPointer right
    let leftBytes ← h.readBytes pointer length
    let rightBytes ← h.readBytes right length
    unless leftBytes.size == length.toNat && rightBytes.size == length.toNat do
      throw (.invalidProgram "memcmp byte-read length mismatch")
    h.writeI32 (compareBytes leftBytes rightBytes) dest
  else if name == "memchr" || name == "memrchr" then
    let needle ← f.readI32 (← arg args 1)
    let length ← f.readUsize (← arg args 2)
    h.checkPointer pointer
    match ← memchr h pointer length (name == "memrchr") (UInt8.ofNat needle.toUInt32.toNat) with
    | some (_,pointer) => f.writePointer pointer dest
    | none => f.writeNull dest
  else if name == "strlen" then
    let bytes ← readCString h budget pointer
    h.writeUsize (UInt64.ofNat bytes.size) dest
  else if name == "wcslen" then
    h.writeUsize (← wcharLength h budget pointer) dest
  else if name == "strnlen" then
    let length ← f.readUsize (← arg args 1)
    h.checkPointer pointer
    let found ← memchr h pointer length false 0
    h.writeUsize (found.map (·.1) |>.getD length) dest
  else if name == "memcpy" then
    let source ← f.readPointer (← arg args 1)
    let length ← f.readUsize (← arg args 2)
    h.checkPointer pointer
    h.checkPointer source
    h.copy source pointer length true
    f.writePointer pointer dest
  else if name == "strcpy" then
    let source ← f.readPointer (← arg args 1)
    let bytes ← readCString h budget source
    if bytes.size+1 ≥ 2^64 then throw (.invalidProgram "strcpy length overflow")
    h.copy source pointer (UInt64.ofNat (bytes.size+1)) true
    f.writePointer pointer dest
  else
    let value ← f.readI32 (← arg args 1)
    let length ← f.readUsize (← arg args 2)
    h.checkPointer pointer
    h.writeRepeatedByte pointer (UInt8.ofNat value.toUInt32.toNat) length
    f.writePointer pointer dest
  return some .NeedsReturn

end Source

def memchr (h : Hooks P S D MD B I) (pointer : Pointer (Option P))
    (count : UInt64) (reverse : Bool) (needle : UInt8) : M S (Option (UInt64 × Pointer (Option P))) := Source.memchr h.core pointer count reverse needle

def readCString (h : Hooks P S D MD B I) (budget : Nat) (pointer : Pointer (Option P)) : M S ByteArray := Source.readCString h.core budget pointer

def wcharLength (h : Hooks P S D MD B I) (budget : Nat) (pointer : Pointer (Option P)) : M S UInt64 := Source.wcharLength h.core budget pointer

def emulate (h : Hooks P S D MD B I) (budget : Nat) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option EmulateItemResult) := Source.emulate h.core budget name abi args dest

/-- Preserve remaining portable source handlers and their fallback ordering. -/
def bind (h : Hooks P S D MD B I) (budget : Nat) :
    ForeignItems.Hooks P S D MD (Pointer (Option P)) B I :=
  { h.foreign with otherPortable := fun name abi args dest => do
      if let some result ← Source.emulate h.core budget name abi args dest then return some result
      h.foreign.otherPortable name abi args dest }

end Miri.Interpreter.MemoryShims
