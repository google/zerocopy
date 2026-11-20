import Miri.Interpreter.TypedSyncTransport
import Miri.Interpreter.FreeBsdSync
import Miri.Interpreter.PthreadSync

/-! Concrete source synchronization dictionaries selected by the final OS
foreign chain. This record owns no state: all identities refer to HostRuntime
and allocation-local metadata built by EvalTypedSyncMachine. -/
namespace Miri.Interpreter.ForeignSyncMachine
open Miri.Concurrency
structure Objects (S : Type) where
  runtime : SyncRuntime.Hooks S TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest
  once : InitOnce.Hooks S TypedSyncRuntime.Ref Int32 TypedSyncRuntime.Dest
  pthread : PthreadObjects.Hooks S TypedSyncRuntime.Ref
  metadata : SyncObject.MetadataHooks S TypedSyncMetadata.Payload
  bytes : TypedSyncObjectMachine.Bytes S
  newFutex : EStateM StepError S TypedSyncRuntime.Ref
  newMacFutex : UInt64 → Bool → EStateM StepError S TypedSyncRuntime.Ref
  macSettings : TypedSyncRuntime.Ref → EStateM StepError S (UInt64 × Bool)
  putMacSettings : TypedSyncRuntime.Ref → UInt64 → Bool → EStateM StepError S Unit

def pthread (objects : Objects S) (h : PthreadSync.Hooks S TypedSyncRuntime.Ref Duration) :=
  {h with objects := objects.pthread}
def windows (objects : Objects S) (h : WindowsSync.Hooks S TypedSyncRuntime.Ref) :=
  {h with once := objects.once, newFutex := objects.newFutex
          metadata := TypedSyncObjectMachine.full objects.metadata objects.bytes TypedSyncObjectMachine.windows}
def mac (objects : Objects S) (h : MacOsSync.Hooks S TypedSyncRuntime.Ref) :=
  {h with runtime := objects.runtime
          newFutex := objects.newMacFutex, settings := objects.macSettings, putSettings := objects.putMacSettings
          futexMetadata := TypedSyncObjectMachine.narrow objects.metadata TypedSyncObjectMachine.macFutex
          lockMetadata := TypedSyncObjectMachine.full objects.metadata objects.bytes TypedSyncObjectMachine.macLock
          semaphoreMetadata := TypedSyncObjectMachine.full objects.metadata objects.bytes TypedSyncObjectMachine.macSemaphore
          newMutex := objects.pthread.newMutex, newSemaphore := objects.pthread.newSemaphore}
def freeBsd (objects : Objects S) (h : FreeBsdSync.Hooks S TypedSyncRuntime.Ref) :=
  {h with runtime := objects.runtime,newFutex := objects.newFutex
          metadata := TypedSyncObjectMachine.narrow objects.metadata TypedSyncObjectMachine.freeBsdFutex}
end Miri.Interpreter.ForeignSyncMachine
