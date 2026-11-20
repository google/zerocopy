import Miri.Interpreter.ThreadStacks
import Miri.Interpreter.FunctionCalls
import Miri.Interpreter.AllocationDriver
import Miri.Interpreter.TlsDestructors

/-! Source thread.rs start_regular_thread / join_thread_exclusive. Thread IDs
own actual ThreadStacks, root calls execute Call.initStackFrame, and captured
join continuations carry canonical typed destinations rather than completion
tokens. TLS closures store the actual source destructor stage. -/
namespace Miri.Interpreter.ThreadMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency Miri.TreeBorrows
abbrev State := ThreadStacks.State
abbrev M := ThreadStacks.M

structure JoinCallback where
  token : Nat
  joined : ThreadId
  result : Scalar Provenance
  destination : MPlaceTy Provenance
structure Runtime (Affinity : Type) where
  nextCallback : Nat := 0
  tlsCallbacks : Array (Nat × TlsDtorsStage Provenance) := #[]
  joins : Array JoinCallback := #[]
  affinity : Option (Array (ThreadId × Affinity)) := none

structure Hooks (K U C Other Extern FnABI ArgABI Affinity : Type) where
  runtime : U → Runtime Affinity
  putRuntime : U → Runtime Affinity → U
  functions : FunctionCalls.Hooks Provenance (State K U) C MachineHooks.FrameExtra Other Extern FnABI ArgABI
  allocation : PlaceMachine.AllocationConfig K (ThreadStacks.Storage U)
  machineMemoryKind : K
  writeScalar : C → Scalar Provenance → MPlaceTy Provenance → M K U Unit
  spans : AllocationDriver.SpanHooks
  /-- Choose only from the source-approved safe vector-clock reuse set. The
  canonical Miri source connector consumes an execution-tape index here; the
  default keeps older non-source adapters fail-closed if they reach reuse. -/
  chooseReuseClock : List VectorIdx → M K U (Option VectorIdx) := fun _ => pure none

private def modifyRuntime (h : Hooks K U C O X F A Aff) (f : Runtime Aff → Runtime Aff) : M K U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := h.putRuntime state.machine.user.user (f (h.runtime state.machine.user.user))}}}
private def runtime (h : Hooks K U C O X F A Aff) : M K U (Runtime Aff) := do
  return h.runtime (← get).machine.user.user
private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error
private def machineAction (action : PlaceMachine.MachineM K (ThreadStacks.Storage U) A) : M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

/-- Real return allocation with source Machine kind visible before root-address
assignment; generic stack allocation's hardcoded Stack kind is not substituted. -/
def allocateReturn [DecidableEq K] (h : Hooks K U C O X F A Aff) (layout : LocalLayout) : M K U (MPlaceTy Provenance) := do
  unless layout.layout.isSized do throw (.invalidProgram "unsized thread return allocation")
  let config := h.allocation
  let size := layout.layout.size
  let align := layout.layout.align.abi
  let allocation ← match Allocation.tryNew (Prov := Provenance) size align .Uninit config.zeroedStorage with
    | .ok allocation => pure allocation
    | .error error => throw (.callback s!"thread return allocation: {reprStr error}")
  if size.bytes > config.maximumObjectSize.bytes then throw (.resourceExhaustion "thread return object too large")
  let state ← get
  let (memory,result) := state.machine.memory.reserveAllocId
  set {state with machine := {state.machine with memory}}
  let id ← match result with
    | .ok id => pure id
    | .error error => throw (.resourceExhaustion s!"thread return allocation id: {reprStr error}")
  machineAction (config.diagnostic id size align)
  let tree ← machineAction (PlaceMachine.initStackExtra config.allocationTail id size align)
  modify fun state => {state with machine := {state.machine with memory := {state.machine.memory with
    live := state.machine.memory.live.push (id,⟨.machine h.machineMemoryKind,allocation.withExtra tree⟩)}}}
  let tag ← match (← get).machine.borrowTracker with
    | none => pure BorTag.one
    | some tracker => match tracker.global.rootTag? id with
      | some tag => pure tag
      | none => throw (.invalidProgram "return allocation missing root tag")
  let pointer ← config.adjustRootAddress id tag
  return ⟨⟨pointer.withOptionalProvenance,.none,none⟩,layout⟩

/-- Bind actual stack/origin operations, retaining compiler ABI and MIR queries.
The real call hooks synchronize all pushed frames, including failure prefixes. -/
def functionHooks (h : Hooks K U C O X F A Aff) :
    FunctionCalls.Hooks Provenance (State K U) C MachineHooks.FrameExtra O X F A :=
  {h.functions with
    call := ThreadStacks.bindCall h.functions.call
    activeStackEmpty := return (← get).stack.frames.isEmpty
    originIsDummy := do
      let manager := (← get).machine.threads
      let some thread := manager.activeThread? | throw (.invalidProgram "active thread missing")
      return thread.originSpanToken == h.spans.dummy.id
    setOrigin := fun span => do
      let manager := (← get).machine.threads
      let some thread := manager.activeThread? | throw (.invalidProgram "active thread missing")
      let thread := {thread with originSpanToken := span.id}
      ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}}

def startRegularThread [DecidableEq K] (h : Hooks K U C O X F A Aff) (choice : C)
    (threadOutput : Option (MPlaceTy Provenance)) (routine : Pointer (Option Provenance))
    (abi : X) (argument : RvalueImmTy Provenance) (returnLayout : LocalLayout)
    (reuseClock : Option VectorIdx) : M K U ThreadId := do
  let span ← AllocationDriver.currentUserRelevantSpan h.spans
  let token := (← runtime h).nextCallback
  modifyRuntime h fun rt => {rt with nextCallback := token+1, tlsCallbacks := rt.tlsCallbacks.push (token,.init)}
  let child ← ThreadStacks.createThread token
  -- Thread::new starts with canonical DUMMY_SP, not the parent call site.
  let manager := (← get).machine.threads
  let some record := manager.thread? child | throw (.invalidProgram "created thread missing")
  let record := {record with originSpanToken := h.spans.dummy.id}
  ThreadStacks.installManager {manager with threads := manager.threads.set child.toNat record}

  if let some global := (← get).machine.dataRace then
    let manager := (← get).machine.threads
    let selected ← match reuseClock with
      | some index => pure (some index)
      | none =>
        let candidates := global.reusableCandidates
        if candidates.isEmpty then pure none else h.chooseReuseClock candidates
    let global ← match global.threadCreated manager child selected with
      | .ok global => pure global
      | .error error => throw (.callback s!"thread-created clocks: {reprStr error}")
    modify fun state => {state with machine := {state.machine with dataRace := some global}}
  if let some output := threadOutput then
    let id ← liftResult (Scalar.fromUInt (BitVec.ofNat 128 child.toNat) output.layout.layout.size |>.mapError ScalarOps.scalarError)
    h.writeScalar choice id output
  let parent ← ThreadStacks.setActiveThread child
  if let some affinity := (← runtime h).affinity then
    if let some (_,cpuset) := affinity.find? (fun entry => entry.1 == parent) then
      modifyRuntime h fun rt => {rt with affinity := some ((affinity.filter fun entry => entry.1 != child).push (child,cpuset))}
  let fnInstance ← match ← h.functions.call.getPtrFn choice routine with
    | .Instance fnInstance => pure fnInstance
    | .Other _ => throw (.unsupported "thread root is not a callable MIR instance")
  let destination ← allocateReturn h returnLayout
  FunctionCalls.callThreadRootFunction (functionHooks h) choice fnInstance abi #[argument] (some destination) span
  let _ ← ThreadStacks.setActiveThread parent
  return child

private def afterJoin (h : Hooks K U C O X F A Aff) (choice : C) (joined : ThreadId)
    (value : Scalar Provenance) (dest : MPlaceTy Provenance) : M K U Unit := do
  let machine := (← get).machine

  if let some global := machine.dataRace then
    let global ← match global.threadJoined machine.threads joined with
      | .ok global => pure global
      | .error error => throw (.callback s!"thread-joined clocks: {reprStr error}")
    modify fun state => {state with machine := {state.machine with dataRace := some global}}
  h.writeScalar choice value dest

def joinExclusive (h : Hooks K U C O X F A Aff) (choice : C) (joined : ThreadId)
    (value : Scalar Provenance) (dest : MPlaceTy Provenance) : M K U Unit := do
  let manager := (← get).machine.threads
  let some thread := manager.thread? joined | throw (.invalidProgram "invalid joined thread")
  if thread.joinStatus == .Joined then throw (.undefinedBehavior "trying to join an already joined thread")
  if joined == manager.activeThread then throw (.undefinedBehavior "trying to join itself")
  if manager.threads.any (fun thread => thread.isBlockedOn (.Join joined)) then
    throw (.invalidProgram "exclusive join already has waiters")
  -- `join_thread_exclusive` performs its Joined/self/waiter checks first,
  -- then delegates to `join_thread`, which rejects Detached before changing
  -- the join status or invoking synchronization/callback effects.
  if thread.joinStatus == .Detached then
    throw (.undefinedBehavior "trying to join a detached thread")
  ThreadStacks.installManager {manager with threads := manager.threads.set joined.toNat {thread with joinStatus := .Joined}}
  if thread.isTerminated then afterJoin h choice joined value dest
  else
    let token := (← runtime h).nextCallback
    modifyRuntime h fun rt => {rt with nextCallback := token+1, joins := rt.joins.push ⟨token,joined,value,dest⟩}
    let manager ← match (← get).machine.threads.blockThread (.Join joined) none token with
      | .ok manager => pure manager
      | .error error => throw (.invalidProgram s!"join block: {reprStr error}")
    ThreadStacks.installManager manager

/-- Invoke in ThreadStacks.unblockThread's selected waiter context. The typed
continuation is consumed before execution; an error retains that context. -/
def takeJoin (h : Hooks K U C O X F A Aff) (token : Nat) : M K U JoinCallback := do
  let rt ← runtime h
  let entries := rt.joins.filter (·.token == token)
  if entries.size != 1 then throw (.callback "missing or ambiguous typed join callback")
  let some callback := entries[0]? | throw (.invalidProgram "join callback lookup invariant")
  modifyRuntime h fun rt => {rt with joins := rt.joins.filter fun entry => entry.token != token}
  pure callback

def resumeJoin (h : Hooks K U C O X F A Aff) (choice : C) (token : Nat) (kind : UnblockKind) : M K U Unit := do
  let callback ← takeJoin h token
  unless kind == .Ready do throw (.invalidProgram "join callback requires Ready")
  afterJoin h choice callback.joined callback.result callback.destination

def threadFromUsize (raw : UInt64) : M K U (Option ThreadId) := do
  match ThreadId.ofNat raw.toNat with
  | .error _ => return none
  | .ok id => return if ((← get).machine.threads.thread? id).isSome then some id else none
end Miri.Interpreter.ThreadMachine
