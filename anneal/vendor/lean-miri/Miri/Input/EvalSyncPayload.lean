import Miri.Interpreter.TypedSyncMetadata
import Miri.Interpreter.TypedSyncObjectMachine
import Miri.Interpreter.LinuxFutexMachine

/-! The source synchronization metadata sum is shared by ordinary MIR memory
extras and callback futex construction. Keep this payload/embedding layer
below EvalConfigurationCore so both source assemblers can depend on it without
an import cycle. -/
namespace Miri.Input.EvalSyncPayload
open Miri.Interpreter Miri.Concurrency

inductive Payload where
  | typed (value : TypedSyncMetadata.Payload)
  | linuxFutex (ref : FutexRuntime.Ref)

def typedEmbedding : TypedSyncObjectMachine.Payload Payload where
  inject := Payload.typed
  project := fun payload => match payload with
    | .typed value => some value
    | .linuxFutex _ => none
  projectInject := fun _ => rfl

def linuxFutexEmbedding : LinuxFutexMachine.Payload Payload where
  inject := Payload.linuxFutex
  project := fun payload => match payload with
    | .linuxFutex ref => some ref
    | .typed _ => none
  projectInject := fun _ => rfl

end Miri.Input.EvalSyncPayload
