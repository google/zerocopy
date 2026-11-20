import Miri.Interpreter.OwnedIoMachine
import Miri.Interpreter.EventFdMachine
import Miri.Interpreter.TypedSyncNat

/-! Source owned IO dictionaries on the actual outer ThreadStacks machine.
Only the already proved full-state reassociation changes record nesting. -/
namespace Miri.Interpreter.OwnedIoTransport
open Miri.Memory Miri.Concurrency
private def action (a : TypedSyncMachine.M K U A) : MachineHooks.M K (ExecutionStateTransport.Outer U) A :=
  ExecutionStateTransport.action a

def event (sync : TypedSyncMachine.Views U) (io : OwnedIoMachine.Views U F)
    (e : TypedSyncMachine.Effects (TypedSyncMachine.State K U))
    (h : OwnedIoMachine.Operations (TypedSyncMachine.State K U) F E) :
    EventFd.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) F :=
  let ops := OwnedIoMachine.hooks io h
  {runtime := TypedSyncNat.outward sync e
   getEvent := fun f => action (h.event.getEvent f)
   putEvent := fun f value => action (h.event.putEvent f value)
   cloneFd := fun f => action (h.event.cloneFd f)
   dropFd := fun f => action (h.event.dropFd f)
   insertNew := fun f => action (h.event.insertNew f)
   libcI32 := fun f => action (h.event.libcI32 f)
   readU32 := fun f => action (h.event.readU32 f)
   readI32 := fun f => action (h.event.readI32 f)
   u64Layout := action h.event.u64Layout
   unaligned := fun p l => action (h.event.unaligned p l)
   readU64 := fun p => action (h.event.readU64 p)
   writeU64 := fun v p => action (h.event.writeU64 v p)
   updateReadiness := fun f => action (h.event.updateReadiness f)
   unblockThread := fun t => action (h.event.unblockThread t)
   deferred := .typed (fun f p c => action (OwnedIoRuntime.readStep ops f p c))
    (fun f p c => action (OwnedIoRuntime.writeStep ops f p c))}

def store (h : EventFdMachine.Store (ExecutionStateTransport.Inner U) O) :
    EventFdMachine.Store (ExecutionStateTransport.Outer U) O where
  get := fun u => h.get (ExecutionStateTransport.toInner u)
  put := fun v u => ExecutionStateTransport.toOuter (h.put v (ExecutionStateTransport.toInner u))
  tag := h.tag
  untag := h.untag
end Miri.Interpreter.OwnedIoTransport
