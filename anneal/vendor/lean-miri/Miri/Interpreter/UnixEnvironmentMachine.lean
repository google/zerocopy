import Miri.Interpreter.UnixEnvironmentDispatch
import Miri.Interpreter.RawMemoryMachine

/-! Canonical machine binding. Host directory/error queries remain stateful
leaves, and source check_ptr_access remains distinct from a memory read/write. -/
namespace Miri.Interpreter.UnixEnvironmentMachine
open Miri.ABI Miri.Memory

def bindMemory [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (arithmetic : PointerArithmetic)
    (strings : OsStrings.Hooks Provenance (MachineHooks.State K U) Os Kind)
    (checkAccess : Pointer (Option Provenance) → UInt64 → MachineHooks.M K U Unit)
    (base : UnixEnvironment.Hooks (MachineHooks.State K U) Os E Kind) :
    UnixEnvironment.Hooks (MachineHooks.State K U) Os E Kind := {
  base with
  strings := strings
  checkAccess := checkAccess
  writeBytes := RawMemoryMachine.writeBytes access arithmetic }
end Miri.Interpreter.UnixEnvironmentMachine
