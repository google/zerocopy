import Miri.Interpreter.FreeBsdSync
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.PlaceMachine

namespace Miri.Interpreter.FreeBsdSyncMachine
open Miri.ABI Miri.Memory

def bindTime (time : TimeShims.Hooks (MachineHooks.State K U) Host System TZ Timestamp)
    (deadline : DeadlineMachine.Hooks K U Host System)
    (base : FreeBsdSync.Hooks (MachineHooks.State K U) R) : FreeBsdSync.Hooks (MachineHooks.State K U) R := {
  base with
  readTimespec := TimeShims.readTimespec time
  parseClockId := TimeShims.parseClockId time
  noIsolation := time.noIsolation
  timeout := DeadlineMachine.timeout deadline }

/-- Regular _umtx_time metadata reads use actual physical scalar reads. The
Acquire load and SeqCst fence remain separate required atomic-engine effects. -/
def bindReads [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (base : FreeBsdSync.Hooks (MachineHooks.State K U) R) : FreeBsdSync.Hooks (MachineHooks.State K U) R :=
  let scalar := fun (place : MPlaceTy Provenance) => do
    let value ← PlaceMachine.readImmediate access ⟨.indirect place.mplace,place.layout⟩
    match value.imm.toScalar with
    | .ok value => pure value | .error error => throw (ScalarOps.immediateError error)
  {base with
    readPlaceScalar := scalar
    readPlaceU32 := fun place => do
      match (← scalar place).toUInt32 with
      | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)}
end Miri.Interpreter.FreeBsdSyncMachine
