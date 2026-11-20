import Miri.Interpreter.EntryArguments
import Miri.Interpreter.MainThread
import Miri.Interpreter.ThreadLoops

/-! Canonical eval.rs main/constructors/exit callback execution. Existing
GlobalConstructors and callMain source policy is reused through transient typed
views; all calls, return memory, TLS, termination and scheduler actions use
actual full machine state and retain failed prefixes. -/
namespace Miri.Interpreter.MainMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency Miri.TreeBorrows
abbrev State := ThreadTlsMachine.State
abbrev M := ThreadTlsMachine.M
abbrev MainView U := MainThreadState Provenance BorrowTree (State U)
structure Data where
  token : Nat
  stage : MainThreadStage Provenance
  constructors : GlobalCtorStage Provenance
  tls : TlsDtorsStage Provenance

structure Hooks (U C O X F A Aff Payload : Type) where
  termination : ThreadTerminationMachine.Hooks U C O X F A Aff Payload
  functions : FunctionPointers.Hooks MiriMemoryKind (ThreadStacks.Storage U) O
  access : PlaceMachine.AccessConfig MiriMemoryKind (ThreadStacks.Storage U)
  layouts : EntryArguments.Layouts
  data : U → Option Data
  putData : U → Option Data → U
  entry : U → MachineGCRoots.EntryPointers
  putEntry : U → MachineGCRoots.EntryPointers → U
  format : ConstructorBinaryFormat
  cNoUnwind : X
  lookupLinkSection : (String → Bool) → M U (Array (TlsImmediate Provenance × SpanRef))
  genericParameters : DefId → M U (Array MainGenericParameter)
  entrySignature : DefId → M U MainSignature
  startLangItem : M U (Option DefId)
  resolveInstance : DefId → Array GenericArg → M U (Option CallInstance)
  layoutOf : TyId → M U LocalLayout

/-- Reassociate the unused termination-payload type parameter. The actual
world payload, TLS/thread hooks, entry roots and every machine action remain
the original ones; no synchronization metadata is converted. -/
def withTerminationPayload (h : Hooks U C O X F A Aff P) : Hooks U C O X F A Aff Q := {
  termination := {
    tls := h.termination.tls
    deallocationError := h.termination.deallocationError
    deallocate := h.termination.deallocate
    }
  functions := h.functions
  access := h.access
  layouts := h.layouts
  data := h.data
  putData := h.putData
  entry := h.entry
  putEntry := h.putEntry
  format := h.format
  cNoUnwind := h.cNoUnwind
  lookupLinkSection := h.lookupLinkSection
  genericParameters := h.genericParameters
  entrySignature := h.entrySignature
  startLangItem := h.startLangItem
  resolveInstance := h.resolveInstance
  layoutOf := h.layoutOf
 }

private def data (h : Hooks U C O X F A Aff P) : M U Data := do
  let some value := h.data (← get).machine.user.user | throw (.invalidProgram "main callback data missing")
  return value
private def putData (h : Hooks U C O X F A Aff P) (value : Option Data) : M U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := h.putData state.machine.user.user value}}}
private def putEntry (h : Hooks U C O X F A Aff P)
    (f : MachineGCRoots.EntryPointers → MachineGCRoots.EntryPointers) : M U Unit :=
  modify fun state =>
    let payload := h.putEntry state.machine.user.user (f (h.entry state.machine.user.user))
    {state with machine := {state.machine with user := {state.machine.user with user := payload}}}
private def liftResult (value : Except StepError A) : M U A :=
  match value with | .ok value => pure value | .error error => throw error

private def tlsView (h : Hooks U C O X F A Aff P) (stage : TlsDtorsStage Provenance) (state : State U) :
    ThreadTlsMachine.Scratch U :=
  let tls := h.termination.tls.data state.machine.user.user
  let memory : ThreadLocalState Provenance BorrowTree (State U) :=
    ⟨state.machine.memory,state,state.machine.threads,tls.statics⟩
  let race := match state.machine.dataRace with | none => .none | some global => .vectorClocks global
  ⟨⟨memory,tls.staticRoots,race⟩,tls.values,stage⟩
private def restoreTls (h : Hooks U C O X F A Aff P) (view : ThreadTlsMachine.Scratch U) : State U :=
  let state := view.exit.tls.hooks
  let tls : ThreadTlsMachine.Data := ⟨view.data,view.exit.tls.pointers,view.exit.staticRoots⟩
  let payload := h.termination.tls.putData state.machine.user.user tls
  {state with machine := {state.machine with
    memory := view.exit.tls.memory
    threads := view.exit.tls.manager
    user := {state.machine.user with user := payload}
    dataRace := match view.exit.race with
      | .none => none | .vectorClocks global => some global}}
private def mainView (h : Hooks U C O X F A Aff P) (value : Data) (state : State U) : MainView U :=
  ⟨⟨tlsView h value.tls state,value.constructors⟩,value.stage,(h.entry state.machine.user.user).mainReturn⟩
private def restoreMain (h : Hooks U C O X F A Aff P) (token : Nat) (view : MainView U) : State U := Id.run do
  let mut state := restoreTls h view.constructors.execution
  let payload := h.putData state.machine.user.user
    (some ⟨token,view.stage,view.constructors.stage,view.constructors.execution.stage⟩)
  state := {state with machine := {state.machine with user := {state.machine.user with user := payload}}}
  let payload := h.putEntry state.machine.user.user
    {h.entry state.machine.user.user with mainReturn := view.mainReturnPlace}
  return {state with machine := {state.machine with user := {state.machine.user with user := payload}}}

private def mainQuery (h : Hooks U C O X F A Aff P) (token : Nat) (action : M U B) :
    MainThreadM Provenance BorrowTree (State U) StepError B := fun view =>
  let state := restoreMain h token view
  -- These are the source closure's local stages, owned by this view; compiler
  -- queries do not choose or reconstruct callback progress.
  let finish (state : State U) :=
    mainView h ⟨token,view.stage,view.constructors.stage,view.constructors.execution.stage⟩ state
  match action state with
  | .ok value state => .ok value (finish state)
  | .error error state => .error (.leaf error) (finish state)

private def immediateArgs (args : Array (OpTy Provenance)) : Except StepError (Array (RvalueImmTy Provenance)) := do
  args.mapM fun value => match value.op with
    | .immediate imm => pure ⟨imm,value.layout⟩
    | .indirect _ => throw (.invalidProgram "main helper argument must be immediate")

def mainQueries (h : Hooks U C O X F A Aff P) (choice : C) (token : Nat) :
    MainThreadQueries Provenance BorrowTree (State U) StepError where
  isizeLayout := h.layouts.isize
  u8Layout := h.layouts.u8
  genericParameters := fun id => mainQuery h token (h.genericParameters id)
  entrySignature := fun id => mainQuery h token (h.entrySignature id)
  startLangItem := mainQuery h token h.startLangItem
  resolveInstance := fun id args => mainQuery h token (h.resolveInstance id args)
  fnPointer := fun fnInstance => mainQuery h token (FunctionPointers.functionPointer h.functions (.Instance fnInstance))
  layoutOf := fun ty => mainQuery h token (h.layoutOf ty)
  allocate := fun layout kind => mainQuery h token do
    unless kind == .machine .machine do throw (.invalidProgram "main return requires Machine allocation")
    ThreadMachine.allocateReturn h.termination.tls.thread layout
  callFunction := fun fnInstance args dest => mainQuery h token do
    let args ← liftResult (immediateArgs args)
    let functions := ThreadMachine.functionHooks h.termination.tls.thread
    FunctionCalls.callFunction functions choice fnInstance functions.call.rustAbi args (some dest) (.stop true)
  readTargetIsize := fun place => mainQuery h token do
    let value ← PlaceMachine.readImmediate h.access ⟨.indirect place.mplace,place.layout⟩
    let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
    liftResult (scalar.toTargetIsize h.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)

private def ctorQuery (h : Hooks U C O X F A Aff P) (action : M U B) :
    GlobalCtorM Provenance BorrowTree (State U) StepError B := fun view =>
  match action (restoreTls h view.execution) with
  | .ok value state => .ok value {view with execution := tlsView h view.execution.stage state}
  | .error error state => .error (.leaf error) {view with execution := tlsView h view.execution.stage state}

def constructors (h : Hooks U C O X F A Aff P) (choice : C) :
    GlobalCtorQueries Provenance BorrowTree (State U) StepError where
  lookupLinkSection := fun predicate => ctorQuery h (h.lookupLinkSection predicate)
  getPointerFnInstance := fun pointer => ctorQuery h do
    match ← FunctionPointers.getPtrFn h.functions pointer with
    | .Instance fnInstance => return fnInstance
    | .Other _ => throw (.unsupported "global constructor is not an instance")
  callConstructor := fun fnInstance span => ctorQuery h
    (FunctionCalls.callThreadRootFunction (ThreadMachine.functionHooks h.termination.tls.thread)
      choice fnInstance h.cNoUnwind #[] none span)

private def mainError (h : Hooks U C O X F A Aff P) : MainThreadError StepError → StepError
  | .leaf error => error
  | .scalar error => ScalarOps.scalarError error
  | .sourceInvariant message => .invalidProgram message
  | .missingStartLangItem => .invalidProgram "could not find start lang item"
  | .unresolvedStartInstance => .invalidProgram "start instance did not resolve"
  | .missingMainReturnPlace => .invalidProgram "main return place missing"
  | .undefinedBehaviorExitCodeOutOfRange value => .undefinedBehavior s!"main exit code outside i32: {value}"
  | .constructor error => h.termination.tls.error error
  | .programExit _ => .invalidProgram "program-exit error outside call_main"

/-- One source main callback invocation, excluding scheduler take/restore.
Existing source ctor/callMain policies execute; exit uses the canonical
ThreadTerminationMachine so TLS/free/join callbacks do not pass through stale
memory-only legacy lifecycle hooks. -/
def invoke (h : Hooks U C O X F A Aff P) (choice : C) : M U StackEmptyPoll := do
  let value ← data h
  match value.stage with
  | .globalConstructors entry entryType argc argv =>
    let view := mainView h value (← get)
    let (poll,ctors) ← match globalConstructorsOnStackEmpty h.format h.termination.tls.target (constructors h choice) view.constructors with
      | .ok poll ctors => pure (poll,ctors)
      | .error error ctors =>
        set (restoreMain h value.token {view with constructors := ctors})
        throw (h.termination.tls.error error)
    let view := {view with constructors := ctors}
    set (restoreMain h value.token view)
    if poll == .Ready then
      match callMain h.termination.tls.target (mainQueries h choice value.token) entry entryType argc argv view with
      | .error error view => set (restoreMain h value.token view); throw (mainError h error)
      | .ok () view => set (restoreMain h value.token {view with stage := .running})
    return .pending
  | .running =>
    let some place := (h.entry (← get).machine.user.user).mainReturn | throw (.invalidProgram "main return place missing")
    let immediate ← PlaceMachine.readImmediate h.access ⟨.indirect place.mplace,place.layout⟩
    let scalar ← liftResult (immediate.imm.toScalar.mapError ScalarOps.immediateError)
    let code ← liftResult (scalar.toTargetIsize h.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    if code.toInt < -(2^31 : Int) || code.toInt >= 2^31 then
      throw (.undefinedBehavior "main exit code outside i32")
    putData h (some {value with stage := .exiting .tls (Int32.ofInt code.toInt), tls := .initForExit})
    return .pending
  | .exiting stage code =>
    match stage with
    | .tls =>
      let view := tlsView h value.tls (← get)
      let (poll,view) ← match tlsOnStackEmpty h.termination.tls.platform h.termination.tls.target
          (ThreadTlsMachine.queries h.termination.tls choice) view with
        | .ok poll view => pure (poll,view)
        | .error error view => set (restoreTls h view); throw (h.termination.tls.error error)
      set (restoreTls h view)
      let stage := if poll == .Ready then
          .yield 256
        else .tls
      putData h (some {value with stage := .exiting stage code, tls := view.stage})
      return .pending
    | .yield remaining =>
      if remaining == 0 then putData h (some {value with stage := .exiting .done code})
      else
        ThreadStacks.installManager (← get).machine.threads.yield
        putData h (some {value with stage := .exiting (.yield (remaining-1)) code})
      return .pending
    | .done =>
      ThreadTerminationMachine.terminate h.termination choice true
      putData h (some {value with stage := .exiting .unreachable code})
      throw (.termination (.exit code.toInt true))
    | .unreachable => throw (.invalidProgram "unreachable main exit handler")

inductive Callback where
  | main (token : Nat)
  | tls (callback : ThreadLoops.TakenTls)

/-- Main and ordinary TLS closures share one actual scheduler callback path.
Each callback is taken once; program-stop/error leaves it consumed. -/
def take (h : Hooks U C O X F A Aff P) : M U Callback := do
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? | throw (.invalidProgram "active callback thread missing")
  if let some main := h.data (← get).machine.user.user then
    if thread.onStackEmptyCallback == some main.token then
      let thread := {thread with originSpanToken := h.termination.tls.thread.spans.dummy.id, onStackEmptyCallback := none}
      ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}
      return .main main.token
  return .tls (← ThreadLoops.take h.termination.tls)

def restore (h : Hooks U C O X F A Aff P) : Callback → M U Unit
  | .tls callback => ThreadLoops.restore h.termination.tls callback
  | .main token => do
    let value ← data h
    unless value.token == token do throw (.invalidProgram "main callback token changed")
    let manager := (← get).machine.threads
    let some thread := manager.activeThread? | throw (.invalidProgram "main callback active thread missing")
    let thread := {thread with onStackEmptyCallback := some token}
    ThreadStacks.installManager {manager with threads := manager.threads.set manager.activeThread.toNat thread}

def bindLoop (h : Hooks U C O X F A Aff P) (base : RunLoopHooks (State U) C Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U) : RunLoopHooks (State U) C Callback :=
  ThreadStacks.bindRunLoop {base with
    takeStackEmptyCallback := fun state => MachineHooks.run (take h) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with | .main _ => invoke h choice | .tls callback => ThreadLoops.invoke h.termination.tls choice callback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run (restore h callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run (ThreadTerminationMachine.terminate h.termination choice forExit) state} scheduler

/-- The final late_init thread step installs the actual captured main stage.
EnvVars and extern-static initialization must precede this source operation. -/
def install (h : Hooks U C O X F A Aff P) (entry : DefId) (entryType : MainEntryType)
    (args : EntryArguments.Arguments) (windows : Bool) : M U Unit := do
  let runtime := h.termination.tls.thread.runtime (← get).machine.user.user
  let token := runtime.nextCallback
  let payload := h.termination.tls.thread.putRuntime (← get).machine.user.user {runtime with nextCallback := token+1}
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with user := payload}}}
  let stage := MainThreadStage.globalConstructors entry entryType
    ⟨args.argc.imm,args.argc.layout⟩ ⟨args.argv.imm,args.argv.layout⟩
  putData h (some ⟨token,stage,.init,.init⟩)
  let manager ← match (← get).machine.threads.initializeMainThread windows token with
    | .ok manager => pure manager | .error error => throw (.invalidProgram s!"main thread init: {reprStr error}")
  ThreadStacks.installManager manager
end Miri.Interpreter.MainMachine
