import Miri.Interpreter.MemoryShims
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.GlobalMemoryCopyMachine
import Miri.Interpreter.PointerMachineBindings

/-! Concrete portable C memory/string shim dictionary. All raw reads/writes,
initialization/provenance checks, race/weak/TB/sync hooks and alignment use the
canonical interpreter machine. Only actual compiler type layouts and foreign
ABI/dispatch policies remain inputs. -/
namespace Miri.Interpreter.MemoryShimMachine
open Miri.ABI Miri.Memory Miri.MIR
abbrev State := PointerMachine.State
abbrev M := PointerMachine.M

structure Hooks (K U C E : Type) where
  access : PlaceMachine.AccessConfig K (PointerMachine.User U)
  pointer : PointerMachine.Hooks K U
  place : PlaceHooks Provenance (State K U) C E
  i32Layout : C → M K U LocalLayout
  usizeLayout : C → M K U LocalLayout
  wcharLayout : C → M K U LocalLayout
  symbolicAlignment : Bool
  enforceAlignment : Bool

private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error

private def writeScalar (h : Hooks K U C E) (choice : C) (expected : LocalLayout)
    (value : Scalar Provenance) (dest : RuntimePlace Provenance) : M K U Unit := do
  if dest.layout != expected then throw (.invalidProgram "memory shim result type/layout mismatch")
  writePlaceImmediate h.place choice (.scalar value) dest

def writeI32 (h : Hooks K U C E) (choice : C) (value : Int32) (dest : RuntimePlace Provenance) : M K U Unit := do
  let layout ← h.i32Layout choice
  unless layout.layout.isSized && layout.layout.size.bytes == 4 do
    throw (.invalidProgram "compiler i32 layout is not four bytes")
  let scalar ← liftResult (Scalar.fromInt value.toInt layout.layout.size |>.mapError ScalarOps.scalarError)
  writeScalar h choice layout scalar dest

def writeUsize (h : Hooks K U C E) (choice : C) (value : UInt64) (dest : RuntimePlace Provenance) : M K U Unit := do
  let layout ← h.usizeLayout choice
  unless layout.layout.isSized do
    throw (.invalidProgram "compiler usize layout is unsized")
  let scalar ← liftResult (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) h.access.runtime.pointerOffset |>.mapError ScalarOps.scalarError)
  writeScalar h choice layout scalar dest

/-- Source read_c_str in MemoryShims scans with readByte and then performs a
second readBytes. Both passes reach real allocation accesses through this
binding; no cached string length suppresses the second read or its hooks. -/
def bind [DecidableEq K] (h : Hooks K U C E) (choice : C)
    (base : MemoryShims.Hooks Provenance (State K U) D (RuntimePlace Provenance) B I) :
    MemoryShims.Hooks Provenance (State K U) D (RuntimePlace Provenance) B I :=
  {base with
    checkPointer := RawMemoryMachine.checkPointer h.access
    readByte := RawMemoryMachine.readByte h.access h.pointer.arithmetic
    readBytes := RawMemoryMachine.readBytes h.access h.pointer.arithmetic
    offset := fun pointer amount => liftResult (RawMemoryMachine.offset h.pointer.arithmetic pointer amount)
    copy := fun source dest size nonoverlapping => GlobalMemoryCopyMachine.copy h.access h.pointer.arithmetic
      source dest (Size.ofBytes size) 1 nonoverlapping
    writeRepeatedByte := RawMemoryMachine.writeRepeatedByte h.access h.pointer.arithmetic
    writeI32 := writeI32 h choice
    writeUsize := writeUsize h choice
    wcharLayout := do
      let layout ← h.wcharLayout choice
      unless layout.layout.isSized do throw (.invalidProgram "unsized libc wchar_t")
      return (layout.layout.size,layout.layout.align.abi)
    checkAlignment := PointerMachine.checkAlignment h.pointer h.symbolicAlignment h.enforceAlignment
    readUnsigned := RawMemoryMachine.readUnsigned h.access h.pointer.arithmetic}
/-- Production construction from source primitives. No whole foreign baseline
or fallback interpreter is requested or captured. -/
def core [DecidableEq K] (h : Hooks K U C E) (choice : C)
    (foreign : ForeignItems.Core Provenance (State K U) D (RuntimePlace Provenance)
      (Pointer (Option Provenance)) B I) :
    MemoryShims.CoreHooks Provenance (State K U) D (RuntimePlace Provenance) B I where
  foreign := foreign
  checkPointer := RawMemoryMachine.checkPointer h.access
  readByte := RawMemoryMachine.readByte h.access h.pointer.arithmetic
  readBytes := RawMemoryMachine.readBytes h.access h.pointer.arithmetic
  offset := fun pointer amount => liftResult (RawMemoryMachine.offset h.pointer.arithmetic pointer amount)
  copy := fun source dest size nonoverlapping => GlobalMemoryCopyMachine.copy h.access h.pointer.arithmetic
    source dest (Size.ofBytes size) 1 nonoverlapping
  writeRepeatedByte := RawMemoryMachine.writeRepeatedByte h.access h.pointer.arithmetic
  writeI32 := writeI32 h choice
  writeUsize := writeUsize h choice
  wcharLayout := do
    let layout ← h.wcharLayout choice
    unless layout.layout.isSized do throw (.invalidProgram "unsized libc wchar_t")
    pure (layout.layout.size,layout.layout.align.abi)
  checkAlignment := PointerMachine.checkAlignment h.pointer h.symbolicAlignment h.enforceAlignment
  readUnsigned := RawMemoryMachine.readUnsigned h.access h.pointer.arithmetic

end Miri.Interpreter.MemoryShimMachine
