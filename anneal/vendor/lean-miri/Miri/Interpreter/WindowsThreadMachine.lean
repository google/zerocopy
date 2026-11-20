import Miri.Interpreter.WindowsThread
import Miri.Interpreter.ThreadTlsMachine

/-! Actual ThreadStacks creation, non-exclusive Windows joining, vector clocks,
and the same TLS storage used by ThreadTlsMachine's destructor engine. -/
namespace Miri.Interpreter.WindowsThreadMachine
open Miri.ABI Miri.Memory Miri.Concurrency

/-- Unlike pthread join, Windows permits repeated joins and joining oneself
blocks. A closed/detached handle remains UB. Continuations use the canonical
ThreadMachine join arena and resumeJoin consumes them before invocation. -/
def join (h : ThreadMachine.Hooks K U C O X F A Aff) (choice : C) (joined : ThreadId)
    (value : Scalar Provenance) (dest : MPlaceTy Provenance) : ThreadMachine.M K U Unit := do
  let manager := (← get).machine.threads
  let some target := manager.thread? joined | throw (.invalidProgram "Windows join thread missing")
  if target.joinStatus == .Detached then throw (.undefinedBehavior "trying to join a detached thread")
  ThreadStacks.installManager {manager with threads := manager.threads.set joined.toNat {target with joinStatus := .Joined}}
  if target.isTerminated then
    let machine := (← get).machine

    if let some global := machine.dataRace then
      let global ← match global.threadJoined machine.threads joined with
        | .ok global => pure global
        | .error error => throw (.callback s!"thread-joined clocks: {reprStr error}")
      modify fun state => {state with machine := {state.machine with dataRace := some global}}
    h.writeScalar choice value dest
  else
    let rt := h.runtime (← get).machine.user.user
    let token := rt.nextCallback
    let rt := {rt with nextCallback := token+1, joins := rt.joins.push ⟨token,joined,value,dest⟩}
    modify fun state => {state with machine := {state.machine with user := {state.machine.user with user := h.putRuntime state.machine.user.user rt}}}
    let manager ← match (← get).machine.threads.blockThread (.Join joined) none token with
      | .ok manager => pure manager
      | .error error => throw (.invalidProgram s!"Windows join block: {reprStr error}")
    ThreadStacks.installManager manager

/-- System ABI is a required target/compiler value, including x86 stdcall. -/
def bind [DecidableEq K] (h : ThreadMachine.Hooks K U C O X F A Aff)
    (choice : C) (systemAbi : X) (reuseClock : Option VectorIdx)
    (base : WindowsThread.Hooks (ThreadStacks.State K U) FD) :
    WindowsThread.Hooks (ThreadStacks.State K U) FD := {
  base with
  handles := {base.handles with threads := return (← get).machine.threads}
  putThreads := ThreadStacks.installManager
  start := fun output routine argument layout =>
    ThreadMachine.startRegularThread h choice output routine systemAbi argument layout reuseClock
  join := join h choice }

/-- TLS and fiber-local keys share exactly the destructor engine's map. -/
def bindTls (h : ThreadTlsMachine.Hooks U C O X F A Aff)
    (base : WindowsThread.Hooks (ThreadTlsMachine.State U) FD) :
    WindowsThread.Hooks (ThreadTlsMachine.State U) FD := {
  base with
  getTls := return (h.data (← get).machine.user.user).values
  putTls := fun values => modify fun state =>
    let data := h.data state.machine.user.user
    {state with machine := {state.machine with user := {state.machine.user with
      user := h.putData state.machine.user.user {data with values}}}} }
/-- Name allocation uses actual lossless host bytes conversion and WinLocal
allocation; no UTF-8-only substitute or invented allocation identity. -/
def bindNames (strings : OsStrings.Hooks Provenance S Os Kind) (winLocal : Kind)
    (base : WindowsThread.Hooks S FD) : WindowsThread.Hooks S FD := {
  base with
  readWide := strings.readWideString
  allocateName := fun bytes => do
    let name ← match OsStrings.bytesToOsStr strings bytes with
      | .ok name => pure name
      | .error error => throw error
    OsStrings.allocOsString strings name winLocal true }
end Miri.Interpreter.WindowsThreadMachine
