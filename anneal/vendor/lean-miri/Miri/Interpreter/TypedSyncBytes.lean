import Miri.Interpreter.TypedSyncFactories
import Miri.Interpreter.RawMemoryMachine

/-! Synchronization marker bytes use the canonical atomic scalar operations and shared memory state. -/

namespace Miri.Interpreter.TypedSyncBytes
open Miri.ABI Miri.Memory Miri.Concurrency
private def lift (result : Except StepError A) : EStateM StepError S A :=
  match result with | .ok value => pure value | .error error => throw error
private def byte (value : UInt8) : EStateM StepError S (Scalar Provenance) :=
  lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 1) |>.mapError ScalarOps.scalarError)

def bindObjectHooks [DecidableEq K]
    (h : LinuxFutexMachine.ObjectHooks K U C P O B) (choice : C)
    (u8Layout : LocalLayout) : TypedSyncObjectMachine.Bytes (LinuxFutexMachine.State K U) where
  checkAccess := fun ptr size => do
    let amount ← lift (sizeAsI64 size |>.mapError fun error => .invalidProgram s!"sync object size: {reprStr error}")
    PointerMachine.checkAccessSigned h.pointers ptr (Int64.ofInt amount) (.dereferenceable "pointer")
  offset := fun place amount => do
    let memory ← h.compiler.memoryOffset choice place.mplace amount .inbounds .none
    pure ⟨memory,u8Layout⟩
  compareExchangeByteRelaxed := fun place expected value => do
    unless place.layout == u8Layout do throw (.invalidProgram "sync marker does not have canonical u8 layout")
    let expected ← byte expected
    let value ← byte value
    let place : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
    let (old,success) ← match ← lift (h.backend (← get)) with
      | .none | .vclocks _ => (IntrinsicAtomic.compareExchange h.atomic choice place
          ⟨.scalar expected,u8Layout⟩ ⟨.scalar value,u8Layout⟩ false .Relaxed .Relaxed)
    let old ← lift (old.toUInt8 |>.mapError ScalarOps.scalarError)
    pure (old,success)
  writeZeros := fun ptr size => RawMemoryMachine.writeRepeatedByte h.access h.pointers.arithmetic ptr 0 size.bytes
  writeByte := fun place value => do
    unless place.layout == u8Layout do throw (.invalidProgram "sync marker does not have canonical u8 layout")
    writePlaceImmediate (ValidityMachine.placeHooks h.access h.allocation h.compiler)
      choice (.scalar (← byte value)) ⟨.memory place.mplace,place.layout⟩

def bind [DecidableEq K]
    (h : LinuxFutexMachine.Hooks K U C P O B H Y Z T E) (choice : C)
    (u8Layout : LocalLayout) : TypedSyncObjectMachine.Bytes (LinuxFutexMachine.State K U) :=
  bindObjectHooks (LinuxFutexMachine.objectHooks h) choice u8Layout
/-- Pthread object compiler globals remain required by their exact source names;
all operand dereferences and byte reads are the canonical physical operations. -/
def pthreadMemoryFromObjectHooks [DecidableEq K]
    (h : LinuxFutexMachine.ObjectHooks K U C P O B) (choice : C)
    (os : String) (initializer : String → LinuxFutexMachine.M K U TypedSyncRuntime.Dest) :
    TypedSyncFactories.PthreadMemory (LinuxFutexMachine.State K U) where
  os := os
  initializer := initializer
  deref := fun op _ => PointerPlaceMachine.dereference h.access h.pointerCompiler h.dynamic h.vtable h.dynamicFuel choice op
  readBytes := fun place size => RawMemoryMachine.readBytes h.access h.pointers.arithmetic place.mplace.ptr size.bytes
  readInitByte := fun place amount => do
    let place ← h.compiler.memoryOffset choice place.mplace amount .inbounds .none
    RawMemoryMachine.readByte h.access h.pointers.arithmetic place.ptr

def pthreadMemory [DecidableEq K]
    (h : LinuxFutexMachine.Hooks K U C P O B H Y Z T E) (choice : C)
    (os : String) (initializer : String → LinuxFutexMachine.M K U TypedSyncRuntime.Dest) :
    TypedSyncFactories.PthreadMemory (LinuxFutexMachine.State K U) :=
  pthreadMemoryFromObjectHooks (LinuxFutexMachine.objectHooks h) choice os initializer
end Miri.Interpreter.TypedSyncBytes
