import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.ForeignItems
import Miri.Interpreter.Unwind

/-! Reassociate the complete foreign primitive dictionary between the actual
Core and Main thread-stack states. Each action transports its result and its
partially updated error state; no guest operation is reconstructed. -/
namespace Miri.Interpreter.ExecutionForeignTransport
open Miri.Memory ExecutionStateTransport

set_option autoImplicit false in
private def mapCore {P S T D MD Ptr B I : Type}
    (run : {A : Type} → EStateM StepError S A → EStateM StepError T A)
    (h : ForeignItems.Core P S D MD Ptr B I) : ForeignItems.Core P T D MD Ptr B I := {
  family := h.family
  os := h.os
  arch := h.arch
  maximumSize := h.maximumSize
  noAllocShimSymbol := h.noAllocShimSymbol
  allocatorSymbol := fun name => run (h.allocatorSymbol name)
  lookupFunction := fun name => run (h.lookupFunction name)
  forceAllocation := fun place => run (h.forceAllocation place)
  returnToBlock := fun block => run (h.returnToBlock block)
  unwindToBlock := fun unwind => run (h.unwindToBlock unwind)
  nativeEnabled := h.nativeEnabled
  callNative := fun name place args => run (h.callNative name place args)
  expectedAbi := fun signature => run (h.expectedAbi signature)
  argumentCompat := fun caller callee => run (h.argumentCompat caller callee)
  checkSymbolClash := fun name => run (h.checkSymbolClash name)
  transmute := fun operand layout => run (h.transmute operand layout)
  readUsize := fun operand => run (h.readUsize operand)
  readPointer := fun operand => run (h.readPointer operand)
  readI32 := fun operand => run (h.readI32 operand)
  isNull := fun pointer => run (h.isNull pointer)
  allocate := fun size align init kind => run (h.allocate size align init kind)
  deallocate := fun pointer layout kind => run (h.deallocate pointer layout kind)
  reallocate := fun pointer old size align kind => run (h.reallocate pointer old size align kind)
  writePointer := fun pointer place => run (h.writePointer pointer place)
  writeNull := fun place => run (h.writeNull place)
  setEnomem := run h.setEnomem
  startExit := fun code => run (h.startExit code)
  specialDestination := fun place => run (h.specialDestination place) }

def core (h : ForeignItems.Core P (MachineHooks.State K (Inner U)) D MD Ptr B I) :
    ForeignItems.Core P (MachineHooks.State K (Outer U)) D MD Ptr B I :=
  mapCore action h

def reverseCore (h : ForeignItems.Core P (MachineHooks.State K (Outer U)) D MD Ptr B I) :
    ForeignItems.Core P (MachineHooks.State K (Inner U)) D MD Ptr B I :=
  mapCore reverseAction h

def hooks (h : ForeignItems.Hooks P (MachineHooks.State K (Inner U)) D MD Ptr B I) :
    ForeignItems.Hooks P (MachineHooks.State K (Outer U)) D MD Ptr B I := {
  toCore := core h.toCore
  math := fun name abi args dest => action (h.math name abi args dest)
  unix := fun name abi args dest => action (h.unix name abi args dest)
  windows := fun name abi args dest => action (h.windows name abi args dest)
  otherPortable := fun name abi args dest => action (h.otherPortable name abi args dest) }

def reverseHooks (h : ForeignItems.Hooks P (MachineHooks.State K (Outer U)) D MD Ptr B I) :
    ForeignItems.Hooks P (MachineHooks.State K (Inner U)) D MD Ptr B I := {
  toCore := reverseCore h.toCore
  math := fun name abi args dest => reverseAction (h.math name abi args dest)
  unix := fun name abi args dest => reverseAction (h.unix name abi args dest)
  windows := fun name abi args dest => reverseAction (h.windows name abi args dest)
  otherPortable := fun name abi args dest => reverseAction (h.otherPortable name abi args dest) }

def unwind (h : Unwind.Hooks K (Inner U) C O) : Unwind.Hooks K (Outer U) C O := {
  payloads := fun user => h.payloads (toInner user)
  setPayloads := fun values user => toOuter (h.setPayloads values (toInner user))
  readImmediate := fun choice operand => action (h.readImmediate choice operand)
  readPointer := fun choice operand => action (h.readPointer choice operand)
  forceAllocation := fun choice place => action (h.forceAllocation choice place)
  getPtrFn := fun choice pointer => action (h.getPtrFn choice pointer)
  callFunction := fun choice callee args continuation => action (h.callFunction choice callee args continuation)
  writeNull := fun choice place => action (h.writeNull choice place)
  writeScalar := fun choice value place => action (h.writeScalar choice value place)
  panicUnwinds := h.panicUnwinds }

end Miri.Interpreter.ExecutionForeignTransport
