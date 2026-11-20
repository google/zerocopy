import Miri.Input.EvalCoreMachine
import Miri.Input.EvalHostMachine
import Miri.Input.EvalBackendMachine

/-! Persistent before_terminator state in the single actual World.host. Source
Control is only a transient view: setter writes both persistent counters and
the existing monotonic clock, preserving every other runtime field. -/
namespace Miri.Input.EvalTerminatorMachine
open Miri.Memory Miri.Interpreter
abbrev Host := HostRuntime.Storage
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalCoreMachine.User Os R P H D O Aff B (Host Poll Instant System H D O Native Profiler)
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler)

/-- Storage access for an opaque real host payload. Production HostRuntime
uses the concrete accessor below; provenance/root traversal is never supplied
by the host accessor. -/
structure ControlAccess (H Clock : Type) where
  get : H → TerminatorMachine.Control Clock
  put : TerminatorMachine.Control Clock → H → H

structure IoSourcesAccess (HostPayload : Type) where
  get : HostPayload → Array (Files.FdId × BlockingIo.Source)
  put : HostPayload → Array (Files.FdId × BlockingIo.Source) → HostPayload

/-- blocking_io.rs::run_gc retains exactly weak descriptions that are not
closed. Liveness comes from the canonical ownership registry, not table slots
or an independently supplied success callback. -/
def ioGc (sources : IoSourcesAccess HostPayload) : MachineHooks.M MiriMemoryKind
    (EvalCoreMachine.User Os R P H D O Aff B HostPayload) Unit := do
  modify fun state =>
    let world := state.machine.user.payload.payload.user
    let live := (sources.get world.host).filter fun entry =>
      !FileOwnership.isClosed world.runtime.ownership entry.2.fd
    let host := sources.put world.host live
    {state with machine := {state.machine with user := {state.machine.user with payload :=
      {state.machine.user.payload with payload := {state.machine.user.payload.payload with user :=
        {world with host}}}}}}

def genericHooks (control : ControlAccess HostPayload Clock)
    (blockingIoGc : MachineHooks.M MiriMemoryKind
      (EvalCoreMachine.User Os R P H D O Aff B HostPayload) Unit) :
    TerminatorMachine.Hooks MiriMemoryKind
      (EvalCoreMachine.User Os R P H D O Aff B HostPayload) Clock where
  getControl := fun user => control.get user.payload.payload.user.host
  setControl := fun value user => {user with payload := {user.payload with payload :=
    {user.payload.payload with user := {user.payload.payload.user with
      host := control.put value user.payload.payload.user.host}}}}
  provenance := {
    visitUser := fun userState initial =>
      MachineGCRoots.visit EvalWorld.roots (ExecutionStateTransport.outward userState) initial
    addresses := fun user => user.addresses
    setAddresses := fun value user => {user with addresses := value}
    symbolicAlignment := fun user => user.symbolicAlignment
    setSymbolicAlignment := fun value user => {user with symbolicAlignment := value} }
  blockingIoGc := blockingIoGc

def getControl (u : User Os R P H D O Aff B Poll Instant System Native Profiler) :
    TerminatorMachine.Control Instant :=
  let host := u.payload.payload.user.host
  TerminatorControl.view host.control host.clock

def setControl (control : TerminatorMachine.Control Instant)
    (u : User Os R P H D O Aff B Poll Instant System Native Profiler) :
    User Os R P H D O Aff B Poll Instant System Native Profiler :=
  {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with host := {u.payload.payload.user.host with
      clock := control.monotonic, control := TerminatorControl.fromView control}}}}}

@[simp] theorem get_set (control : TerminatorMachine.Control Instant)
    (u : User Os R P H D O Aff B Poll Instant System Native Profiler) :
    getControl (setControl control u) = control := by
  simp only [getControl,setControl,TerminatorControl.view_fromView]

def controlAccess : ControlAccess (Host Poll Instant System H D O Native Profiler) Instant where
  get := fun host => TerminatorControl.view host.control host.clock
  put := fun value host => {host with clock := value.monotonic, control := TerminatorControl.fromView value}

def ioSourcesAccess : IoSourcesAccess (Host Poll Instant System H D O Native Profiler) where
  get := fun host => host.blocking.sources
  put := fun host sources => {host with blocking := {host.blocking with sources}}

def hooks (blockingIoGc : MachineHooks.M MiriMemoryKind
    (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit) :
    TerminatorMachine.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Instant :=
  genericHooks controlAccess blockingIoGc
/-- Production binding replaces all control storage callbacks with the actual
source host state. The sole surviving operation is real blocking-I/O GC. -/
def bind (blockingIoGc : MachineHooks.M MiriMemoryKind
    (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (base : ExecutionMachine.Config MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) C O X Instant) :
    ExecutionMachine.Config MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) C O X Instant :=
  {base with terminators := hooks blockingIoGc}
end Miri.Input.EvalTerminatorMachine
