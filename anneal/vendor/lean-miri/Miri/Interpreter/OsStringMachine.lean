import Miri.Interpreter.OsStrings
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.PointerMachineBindings
import Miri.Interpreter.MiriShims

/-! Actual raw-memory binding for source OS-string helpers. UTF-16 reads use
one aligned integer access per element; writes acquire the full destination
once, as source get_ptr_alloc_mut does, preserving source race/borrow events.
-/
namespace Miri.Interpreter.OsStringMachine
open Miri.ABI Miri.Memory
abbrev State := PointerMachine.State
abbrev M := PointerMachine.M

structure Hooks (K U : Type) where
  access : PlaceMachine.AccessConfig K (PointerMachine.User U)
  pointer : PointerMachine.Hooks K U
  symbolicAlignment : Bool
  enforceAlignment : Bool

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error

private def readWideLoop [DecidableEq K] (h : Hooks K U) :
    Nat → Pointer (Option Provenance) → Array UInt16 → M K U (Array UInt16)
  | 0,_,_ => throw (.resourceExhaustion "UTF-16 string scan budget")
  | fuel+1,pointer,values => do
    let value ← RawMemoryMachine.readUnsigned h.access h.pointer.arithmetic pointer (Size.ofBytes 2)
    if value == 0 then return values
    if value.toNat >= 2^16 then throw (.invalidProgram "UTF-16 scalar conversion exceeds u16")
    let pointer ← lift (RawMemoryMachine.offset h.pointer.arithmetic pointer 2)
    readWideLoop h fuel pointer (values.push (UInt16.ofNat value.toNat))

def readWideString [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (pointer : Pointer (Option Provenance)) : M K U (Array UInt16) := do
  PointerMachine.checkAlignment h.pointer h.symbolicAlignment h.enforceAlignment pointer ⟨1⟩
  readWideLoop h budget pointer #[]

private def encodeUnit (endian : Endian) (unit : UInt16) : Array UInt8 :=
  let low := UInt8.ofNat (unit.toNat % 256)
  let high := UInt8.ofNat (unit.toNat / 256)
  match endian with | .little => #[low,high] | .big => #[high,low]

def writeWideString [DecidableEq K] (h : Hooks K U) (units : Array UInt16)
    (pointer : Pointer (Option Provenance)) (capacity : UInt64) : M K U (Bool × UInt64) := do
  let count := units.size+1
  if count >= 2^64 then throw (.invalidProgram "UTF-16 string length overflow")
  let needed := UInt64.ofNat count
  if capacity < needed then return (false,needed)
  PointerMachine.checkAlignment h.pointer h.symbolicAlignment h.enforceAlignment pointer ⟨1⟩
  if count*2 >= 2^64 then throw (.invalidProgram "UTF-16 Size multiplication overflow")
  let bytes := (units.push 0).flatMap (encodeUnit h.access.runtime.base.endian)
  RawMemoryMachine.writeBytes h.access h.pointer.arithmetic pointer ⟨bytes⟩
  return (true,needed)

/-- Retain exact actual host encoding and runtime array-layout/allocator leaves.
Missing compiler-created runtime array types are never replaced by byte views. -/
def bind [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (memory : MemoryShims.Hooks Provenance (State K U) D MD B I)
    (base : OsStrings.Hooks Provenance (State K U) Os Kind) :
    OsStrings.Hooks Provenance (State K U) Os Kind :=
  { base with
    readCString := MemoryShims.readCString memory budget
    readWideString := readWideString h budget
    writeCString := RawMemoryMachine.writeCString h.access h.pointer.arithmetic
    writeWideString := writeWideString h }

/-- miri_host_to_target_path reads a plain host OsStr, then performs only the
HostToTarget conversion on output; reading a target path here would convert twice. -/
def bindMiri (strings : OsStrings.Hooks Provenance S Os Kind)
    (base : MiriShims.Hooks Provenance S D MD B I Os) :
    MiriShims.Hooks Provenance S D MD B I Os :=
  { base with
    readHostPath := OsStrings.readOsString strings
    writeTargetPath := fun path output size => OsStrings.writePath strings path output size }

end Miri.Interpreter.OsStringMachine
