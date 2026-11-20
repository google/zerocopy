import Miri.Interpreter.PollDispatch
import Miri.Interpreter.ReadinessMachine
import Miri.Interpreter.DeadlineMachine

/-! Canonical machine ownership/clock binding for poll and epoll. Other payload
injection/downcast is explicit so an unavailable descriptor cannot masquerade
as an epoll instance. The source Epoll does not contain ReadinessWatched. -/
namespace Miri.Interpreter.PollMachine
open Miri.Memory Files
structure Epoll where
  watcher : Nat
  deriving DecidableEq, Repr

def name (_ : Epoll) : String := "epoll"
def metadata (_ : Epoll) : String := "S_IFREG"
structure DescriptorHooks (O : Type) where
  inject : Epoll → O
  project : O → Option Epoll

private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Owning transfer into the real descriptor table; no extra watcher retain. -/
def insertEpoll (h : ReadinessMachine.Hooks K U H D O) (descriptor : DescriptorHooks O)
    (watcher : Nat) : MachineHooks.M K U Int32 := do
  let value := descriptor.inject ⟨watcher⟩
  if descriptor.project value != some ⟨watcher⟩ then
    throw (.invalidProgram "Epoll descriptor injection/downcast mismatch")
  let ref ← FileMachine.newReference h.files (.other value)
  let (table,number) ← lift ((h.files.table (← get).machine.user).insert ref)
  modify fun state => { state with machine := { state.machine with user := h.files.setTable table state.machine.user } }
  return number

/-- Call at actual Epoll watcher-field drop, after strong FD count reaches zero. -/
def dropEpoll (h : ReadinessMachine.Hooks K U H D O)
    (base : Readiness.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)))
    (epoll : Epoll) : MachineHooks.M K U Unit :=
  (ReadinessMachine.bind h base).dropWatcher epoll.watcher

def bind (h : ReadinessMachine.Hooks K U H D O) (descriptor : DescriptorHooks O)
    (deadline : DeadlineMachine.Hooks K U Host System)
    (base : EpollShims.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)) I) :
    EpollShims.Hooks (MachineHooks.State K U) (Files.Ref (Description H D O)) I := {
  base with
  poll := { base.poll with
    readiness := ReadinessMachine.bind h base.poll.readiness
    newWatcher := ReadinessMachine.newWatcher h
    lookupFd := fun number => do
      match (h.files.table (← get).machine.user).get number with
      | none => return none
      | some ref => return some (← FileMachine.cloneReference h.files ref)
    deadlineMillis := DeadlineMachine.monotonicDeadlineMillis deadline }
  insertEpoll := insertEpoll h descriptor
  asEpoll := fun ref => pure (match ref.value with
    | .other value => (descriptor.project value).map Epoll.watcher
    | _ => none) }

/-- Uses actual mio poll(0) and source Interrupted policy via BlockingIo. -/
def bindEntryPoll (budget : Nat) (io : BlockingIo.Hooks S F P H)
    (base : PollDispatch.Hooks S F I) : PollDispatch.Hooks S F I := {
  base with pollAndUnblockZero := BlockingIo.pollAndUnblock budget io (some ⟨0,0,by decide⟩) }
end Miri.Interpreter.PollMachine
