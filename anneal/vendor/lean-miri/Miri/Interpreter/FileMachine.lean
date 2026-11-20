import Miri.Interpreter.FileOwnership
import Miri.Interpreter.UnixFd
import Miri.Interpreter.MachineHooks

/-! Canonical machine binding of descriptor tables and ownership. Pending I/O
must retain/transfer actual references via these same operations. Host resource
close and readiness destruction remain explicit last-drop effects. -/
namespace Miri.Interpreter.FileMachine
open Files
structure Hooks (K U H D O : Type) where
  table : U → Files.Table (Description H D O)
  setTable : Files.Table (Description H D O) → U → U
  ownership : U → FileOwnership.Registry (Description H D O)
  setOwnership : FileOwnership.Registry (Description H D O) → U → U
  hostUsizeBits : Nat
  referenceBudget : Nat
  onLastDrop : Description H D O → MachineHooks.M K U Unit
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

def newReference (h : Hooks K U H D O) (value : Description H D O) : MachineHooks.M K U (Files.Ref (Description H D O)) := do
  let user := (← get).machine.user
  let (table,ref) ← lift ((h.table user).newRef value h.hostUsizeBits)
  modify fun state => { state with machine := { state.machine with user := h.setTable table state.machine.user } }
  let ownership ← lift (FileOwnership.register (h.ownership (← get).machine.user) ref)
  modify fun state => { state with machine := { state.machine with user := h.setOwnership ownership state.machine.user } }
  return ref

def cloneReference (h : Hooks K U H D O) (ref : Files.Ref (Description H D O)) : MachineHooks.M K U (Files.Ref (Description H D O)) := do
  let (ownership,ref) ← lift (FileOwnership.retain (h.ownership (← get).machine.user) ref.id h.referenceBudget)
  modify fun state => { state with machine := { state.machine with user := h.setOwnership ownership state.machine.user } }
  return ref

def dropReference (h : Hooks K U H D O) (ref : Files.Ref (Description H D O)) : MachineHooks.M K U Unit := do
  let (ownership,last) ← lift (FileOwnership.release (h.ownership (← get).machine.user) ref.id)
  modify fun state => { state with machine := { state.machine with user := h.setOwnership ownership state.machine.user } }
  if let some value := last then h.onLastDrop value

def upgradeWeak (h : Hooks K U H D O) (weak : Files.WeakRef) : MachineHooks.M K U (Option (Files.Ref (Description H D O))) := do
  let (ownership,ref) ← lift (FileOwnership.upgrade (h.ownership (← get).machine.user) weak h.referenceBudget)
  modify fun state => { state with machine := { state.machine with user := h.setOwnership ownership state.machine.user } }
  return ref

def bind (h : Hooks K U H D O) (base : UnixFd.Hooks (MachineHooks.State K U) H D O E Meta) :
    UnixFd.Hooks (MachineHooks.State K U) H D O E Meta := {
  base with
  table := do return h.table (← get).machine.user
  putTable := fun table => modify fun state =>
    { state with machine := { state.machine with user := h.setTable table state.machine.user } }
  newReference := newReference h
  cloneRef := cloneReference h
  dropRef := dropReference h }

def init (h : Hooks K U H D O) (mute : Bool) : MachineHooks.M K U Unit := do
  let table := h.table (← get).machine.user
  if !table.fds.isEmpty || table.nextId != 0 || !(h.ownership (← get).machine.user).entries.isEmpty then
    throw (.invalidProgram "file table initialization requires fresh ownership state")
  for value in #[Description.stdin, (if mute then .nullOutput else .stdout), (if mute then .nullOutput else .stderr)] do
    let ref ← newReference h value
    let (table,_) ← lift ((h.table (← get).machine.user).insert ref)
    modify fun state => { state with machine := { state.machine with user := h.setTable table state.machine.user } }
end Miri.Interpreter.FileMachine
