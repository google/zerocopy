import Miri.Interpreter.BlockingIo
import Miri.Interpreter.ReadinessMachine
import Miri.Interpreter.DeadlineMachine
import Miri.Concurrency.FutexRuntime
import Miri.Concurrency.TypedSyncRuntime
import Miri.Interpreter.TerminatorControl
import Miri.Interpreter.OwnedIoRuntime
import Miri.Interpreter.OwnedIoStore

/-! Typed source host-owned machine.rs::new state. Host effects are required
operations on an actual environment; isolated mode still creates then drops the
poll object, while the clock uses the source virtual epoch. No closure arena is
embedded recursively in its own machine state. -/
namespace Miri.Input.HostRuntime
open Miri.Memory Miri.Interpreter Miri.Concurrency
structure Storage (Poll Instant System H D O Native Profiler : Type) where
  blocking : BlockingIo.Manager Poll
  clock : Clock.Monotonic Instant
  deadlines : DeadlineMachine.Registry Instant System
  readiness : ReadinessMachine.Registry (Files.Ref (Files.Description H D O))
  futex : FutexRuntime.Storage (MPlaceTy Provenance)
  sync : TypedSyncRuntime.Storage
  io : OwnedIoStore.Storage (Files.Ref (Files.Description H D O))
  events : Array (Files.FdId × EventFd.Event)
  virtualSockets : Array (Files.FdId × VirtualSocket.State)
  tcpSockets : Array (Files.FdId × O)
  nativeLibraries : Array (String × Native)
  profiler : Option Profiler
  control : TerminatorControl.Counters

structure Configuration where
  communicate : Bool
  muteOutput : Bool
  hostUsizeBits : Nat
  profileOutput : Option String
  nativeLibraries : Array String
  hostTriple : String
  targetTriple : String
  nativeSupported : Bool
  control : TerminatorControl.Configuration

structure Hooks (S Poll Instant System Native Profiler : Type) where
  createProfiler : String → EStateM StepError S Profiler
  newPoll : EStateM StepError S Poll
  dropPoll : Poll → EStateM StepError S Unit
  hostClock : Clock.HostHooks Instant System S
  loadNative : String → EStateM StepError S Native
  dropNative : Native → EStateM StepError S Unit
  dropProfiler : Profiler → EStateM StepError S Unit

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw error

/-- Source owns partially created resources on all failure outcomes. Cleanup
runs in reverse field-construction order and retains the original failure;
cleanup failures remain visible when construction itself succeeded. -/
private def onError (action : EStateM StepError S A) (cleanup : EStateM StepError S Unit) :
    EStateM StepError S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state =>
    match cleanup state with
    | .ok _ state | .error _ state => .error error state

def create (h : Hooks S Poll Instant System Native Profiler) (config : Configuration)
    (beforePoll beforeDescriptors : EStateM StepError S Unit) :
    EStateM StepError S (Storage Poll Instant System H D O Native Profiler ×
      Files.Table (Files.Description H D O) × FileOwnership.Registry (Files.Description H D O)) := do
  let profiler ← match config.profileOutput with
    | none => pure none | some output => pure (some (← h.createProfiler output))
  onError (do
    beforePoll
    let poll ← h.newPoll
    let blocking ← if config.communicate then pure (BlockingIo.Manager.mk (some poll) #[])
      else do h.dropPoll poll; pure ⟨none,#[]⟩
    onError (do
      beforeDescriptors
      let descriptors ← lift (Files.Table.init config.muteOutput config.hostUsizeBits)
      let mut ownership : FileOwnership.Registry (Files.Description H D O) := {}
      for (_,reference) in descriptors.fds do ownership ← lift (FileOwnership.register ownership reference)
      let clock ← Clock.Monotonic.new h.hostClock config.communicate
      let rec load (remaining : List String) : EStateM StepError S (Array (String × Native)) := do
        match remaining with
        | [] => return #[]
        | path::rest =>
          unless config.nativeSupported do throw (.unsupported "native libraries unsupported in this source build")
          unless config.hostTriple == config.targetTriple do
            throw (.invalidProgram "native library requires identical host and target triples")
          let library ← h.loadNative path
          let later ← onError (load rest) (h.dropNative library)
          return #[(path,library)] ++ later
      let libraries ← load config.nativeLibraries.toList
      return ({
        blocking := blocking
        clock := clock
        deadlines := .empty
        readiness := {watched := descriptors.fds.map fun (_,reference) => (reference.id,{})}
        futex := {}
        sync := {}
        io := {}
        events := #[]
        virtualSockets := #[]
        tcpSockets := #[]
        nativeLibraries := libraries
        profiler := profiler
        control := TerminatorControl.initial config.control},descriptors,ownership)
    ) (match blocking.poll with | none => pure () | some poll => h.dropPoll poll)
  ) (match profiler with | none => pure () | some profiler => h.dropProfiler profiler)
/-- Cleanup for a fully constructed host payload if later machine assembly fails. -/
def dispose (h : Hooks S Poll Instant System Native Profiler)
    (host : Storage Poll Instant System H D O Native Profiler) : EStateM StepError S Unit := do
  for (_,library) in host.nativeLibraries.toList.reverse do h.dropNative library
  if let some poll := host.blocking.poll then h.dropPoll poll
  if let some profiler := host.profiler then h.dropProfiler profiler

def protect (h : Hooks S Poll Instant System Native Profiler)
    (host : Storage Poll Instant System H D O Native Profiler) (action : EStateM StepError S A) :
    EStateM StepError S A := onError action (dispose h host)
end Miri.Input.HostRuntime
