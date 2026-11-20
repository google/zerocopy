import Miri.Interpreter.OwnedSocketOperations

/-! Full state reassociation for source socket operations. Finish captures retain
exact environments, and transient bodies are translated in the inverse direction.
No callbacks or additional roots are installed by this transport. -/
namespace Miri.Interpreter.OwnedSocketTransport
open Miri.Memory Miri.Concurrency
private def action (a : TypedSyncMachine.M K U A) : MachineHooks.M K (ExecutionStateTransport.Outer U) A :=
  ExecutionStateTransport.action a
private def finish (f : Socket.Finish (MachineHooks.State K (ExecutionStateTransport.Outer U)) E A) :
    Socket.Finish (TypedSyncMachine.State K U) E A :=
  ⟨fun result => ExecutionStateTransport.reverseAction (f result),f.capture⟩

def socket (h : Socket.Hooks (TypedSyncMachine.State K U) F E I)
    (base : Socket.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) F E I) :
    Socket.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) F E I :=
  {base with
   os := h.os
   communicate := h.communicate
   operations := {
    bind := fun f c a => action (h.operations.bind f c a)
    listen := fun f c n => action (h.operations.listen f c n)
    accept := fun f c n k => action (h.operations.accept f c n (finish k))
    connect := fun f c a k => action (h.operations.connect f c a (finish k))
    send := fun f c p n b k => action (h.operations.send f c p n b (finish k))
    recv := fun f c p n peek b k => action (h.operations.recv f c p n peek b (finish k))
    setOption := fun f l o p n => action (h.operations.setOption f l o p n)
    getOption := fun f l o => action (h.operations.getOption f l o)
    localName := fun f c => action (h.operations.localName f c)
    peerName := fun f c k => action (h.operations.peerName f c (finish k))
    shutdown := fun f c how => action (h.operations.shutdown f c how)}
   lookupFd := fun n => action (h.lookupFd n)
   asSocket := fun f => action (h.asSocket f)
   dropFd := fun f => action (h.dropFd f)
   newTcp := fun family nonblock => action (h.newTcp family nonblock)
   insert := fun f => action (h.insert f)}
def readiness (h : Readiness.Hooks (TypedSyncMachine.State K U) F)
    (runtime : SyncRuntime.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) Nat Int32 (MPlaceTy Provenance)) :
    Readiness.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) F :=
  {runtime,debugAssertions := h.debugAssertions
   getWatcher := fun n => action (h.getWatcher n)
   putWatcher := fun n w => action (h.putWatcher n w)
   upgradeWatcher := fun n => action (h.upgradeWatcher n)
   dropWatcher := fun n => action (h.dropWatcher n)
   watcherAlive := fun n => action (h.watcherAlive n)
   getFd := fun n => action (h.getFd n)
   id := h.id,downgrade := h.downgrade
   upgrade := fun w => action (h.upgrade w)
   dropFd := fun f => action (h.dropFd f)
   isClosed := fun w => action (h.isClosed w)
   supportsWatching := h.supportsWatching
   getWatched := fun f => action (h.getWatched f)
   putWatched := fun f w => action (h.putWatched f w)
   readiness := fun f => action (h.readiness f)
   delayed := action h.delayed
   putDelayed := fun fs => action (h.putDelayed fs)
   unblock := fun t r => action (h.unblock t r)}

def virtual (h : VirtualSocket.Hooks (TypedSyncMachine.State K U) F E)
    (runtime : SyncRuntime.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) Nat Int32 (MPlaceTy Provenance))
    (base : VirtualSocket.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) F E) :=
  {base with
   readiness := readiness h.readiness runtime
   get := fun f => action (h.get f)
   put := fun f v => action (h.put f v)
   newSocket := fun v => action (h.newSocket v)
   insert := fun f => action (h.insert f)
   readBytes := fun p n => action (h.readBytes p n)
   writeBytes := fun p b => action (h.writeBytes p b)
   os := h.os,wakeBudget := h.wakeBudget}

def files (h : Files.Hooks (TypedSyncMachine.State K U) H D O E Meta)
    (base : Files.Hooks (MachineHooks.State K (ExecutionStateTransport.Outer U)) H D O E Meta) :=
  {base with
   otherRead := fun f c p n k => action (h.otherRead f c p n
     ⟨fun result => ExecutionStateTransport.reverseAction (k result),k.capture⟩)
   otherWrite := fun f c p n k => action (h.otherWrite f c p n
     ⟨fun result => ExecutionStateTransport.reverseAction (k result),k.capture⟩)
   otherShortOperations := h.otherShortOperations
   otherHasReadinessWatched := h.otherHasReadinessWatched
   otherReadiness := fun p => action (h.otherReadiness p)}
end Miri.Interpreter.OwnedSocketTransport
