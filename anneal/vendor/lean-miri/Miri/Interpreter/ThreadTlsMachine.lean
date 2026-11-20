import Miri.Interpreter.ThreadMachine

/-! Execute the existing source TLS destructor state machine against canonical
machine memory, actual frames, and thread manager. The legacy engine view is
transient: every compiler/root-call query restores the latest full state and
recaptures it on both outcomes. No persistent memory/clock copy is stored. -/
namespace Miri.Interpreter.ThreadTlsMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency Miri.TreeBorrows
abbrev State U := ThreadStacks.State MiriMemoryKind U
abbrev M U A := ThreadStacks.M MiriMemoryKind U A
abbrev Scratch U := TlsExecutionState Provenance BorrowTree (State U)
abbrev SM U A := TlsM Provenance BorrowTree (State U) StepError A

structure Data where
  values : ThreadTlsData Provenance
  statics : Array (ThreadLocalEntry Provenance)
  staticRoots : Array AllocId

structure Hooks (U C O X F A Aff : Type) where
  thread : ThreadMachine.Hooks MiriMemoryKind U C O X F A Aff
  data : U → Data
  putData : U → Data → U
  target : RuntimeTargetDataLayout
  platform : TlsPlatform
  unitPtrMut : LocalLayout
  unitPtrConst : LocalLayout
  u32Layout : LocalLayout
  lookupLinkSection : String → M U (Array (TlsImmediate Provenance × SpanRef))
  evalWindows : String → String → M U (Scalar Provenance)
  abi : TlsCallAbi → X
  error : TlsExecutionError StepError → StepError

private def capture (h : Hooks U C O X F A Aff) (stage : TlsDtorsStage Provenance) (state : State U) : Scratch U :=
  let data := h.data state.machine.user.user
  let tls : ThreadLocalState Provenance BorrowTree (State U) := {
    memory := state.machine.memory
    hooks := state
    manager := state.machine.threads
    pointers := data.statics }
  let race := match state.machine.dataRace with
    | none => .none | some global => .vectorClocks global
  {exit := ⟨tls,data.staticRoots,race⟩, data := data.values, stage}

private def restore (h : Hooks U C O X F A Aff) (scratch : Scratch U) : State U :=
  let state := scratch.exit.tls.hooks
  let data : Data := ⟨scratch.data,scratch.exit.tls.pointers,scratch.exit.staticRoots⟩
  let user := {state.machine.user with user := h.putData state.machine.user.user data}
  {state with machine := {state.machine with
    memory := scratch.exit.tls.memory
    threads := scratch.exit.tls.manager
    user
    dataRace := match scratch.exit.race with
      | .none => none | .vectorClocks global => some global}}

/-- Compiler queries and real destructor calls preserve the engine's preceding
stage/data mutations and every failed full-state query effect. -/
private def query (h : Hooks U C O X F A Aff) (action : M U B) : SM U B := fun scratch =>
  let state := restore h scratch
  match action state with
  | .ok value state => .ok value (capture h scratch.stage state)
  | .error error state => .error (.leaf error) (capture h scratch.stage state)

def queries (h : Hooks U C O X F A Aff) (choice : C) :
    TlsDestructorQueries Provenance BorrowTree (State U) StepError where
  unitPtrMut := h.unitPtrMut
  unitPtrConst := h.unitPtrConst
  u32Layout := h.u32Layout
  lookupLinkSection := fun sectionName => query h (h.lookupLinkSection sectionName)
  evalWindows := fun lib name => query h (h.evalWindows lib name)
  getPointerFnInstance := fun pointer => query h do
    match ← h.thread.functions.call.getPtrFn choice pointer with
    | .Instance fnInstance => return fnInstance
    | .Other _ => throw (.unsupported "TLS destructor is not a callable MIR instance")
  callThreadRootFunction := fun fnInstance abi args span => query h do
    let mut values : Array (RvalueImmTy Provenance) := #[]
    for value in args do
      match value.op with
      | .immediate imm => values := values.push ⟨imm,value.layout⟩
      | .indirect _ => throw (.invalidProgram "TLS root argument must be immediate")
    FunctionCalls.callThreadRootFunction (ThreadMachine.functionHooks h.thread) choice fnInstance (h.abi abi) values none span

private def changeRuntime (h : Hooks U C O X F A Aff)
    (f : ThreadMachine.Runtime Aff → ThreadMachine.Runtime Aff) : M U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := h.thread.putRuntime state.machine.user.user (f (h.thread.runtime state.machine.user.user))}}}

/-- scheduler.rs run_on_stack_empty: reset origin, take the callback, run its
real captured stage, restore it only on success. Errors retain the callback's
consumption and all earlier destructor state/frame/memory effects. -/
def onStackEmpty (h : Hooks U C O X F A Aff) (choice : C) : M U StackEmptyCallbackResult := do
  unless (← get).stack.frames.isEmpty do throw (.invalidProgram "TLS callback requires actual empty stack")
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "active TLS thread missing")
  let thread := {thread with originSpanToken := h.thread.spans.dummy.id}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
  let some token := thread.onStackEmptyCallback | throw (.invalidProgram "thread has no stack-empty callback")
  let manager := (← get).machine.threads
  let thread := {thread with onStackEmptyCallback := none}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
  let runtime := h.thread.runtime (← get).machine.user.user
  let some (_,stage) := runtime.tlsCallbacks.find? (fun entry => entry.1 == token) |
    throw (.unsupported "stack-empty callback is not a registered TLS closure")
  changeRuntime h fun runtime => {runtime with tlsCallbacks := runtime.tlsCallbacks.filter fun entry => entry.1 != token}
  let scratch := capture h stage (← get)
  let (result,scratch) ← match tlsOnStackEmpty h.platform h.target (queries h choice) scratch with
    | .ok result scratch => pure (result,scratch)
    | .error error scratch =>
      set (restore h scratch)
      throw (h.error error)
  set (restore h scratch)
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "TLS callback removed active thread")
  let thread := {thread with onStackEmptyCallback := some token}
  ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
  changeRuntime h fun runtime => {runtime with tlsCallbacks := runtime.tlsCallbacks.push (token,scratch.stage)}
  return result
end Miri.Interpreter.ThreadTlsMachine
