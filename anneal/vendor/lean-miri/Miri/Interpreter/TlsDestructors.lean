import Miri.Interpreter.ThreadTls

/-! Pinned shims/tls.rs::TlsDtorsState::on_stack_empty (247-345),
schedule_thread_atexit (392-417), schedule_next_pthread_tls_dtor (423-460),
schedule_next_windows_fls_dtor (465-531), schedule_windows_tls_dtor (365-389).
Each call schedules an actual canonical instance call; Pending is not success
of the destructor body. Re-entry occurs only after its stack becomes empty. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency

inductive TlsTargetOs where
  | linux | macos | windows | other (name : String)
structure TlsPlatform where
  unix : Bool
  os : TlsTargetOs
inductive TlsCallAbi where
  | cNoUnwind | systemNoUnwind
structure TlsImmediate (P : Type) where
  value : Immediate P
  layout : TyAndLayout MIR.TyId
inductive TlsDtorsStage (P : Type) where
  | init
  | initForExit
  | pthread (lastKey : Option TlsKey)
  | afterPthread
  | threadAtexit
  | windows (lastKey : Option TlsKey) (remainingKeys : List TlsKey)
      (callbacks : Array (TlsImmediate P × MIR.SpanRef))
  | done
inductive TlsExecutionError (Error : Type) where
  | tls (error : ThreadTlsError)
  | immediate (error : ImmediateError)
  | scalar (error : ScalarError)
  | exit (error : ThreadExitError Error)
  | leaf (error : Error)
  deriving Repr
structure TlsExecutionState (P E H : Type) where
  exit : ThreadExitState P E H
  data : ThreadTlsData P
  stage : TlsDtorsStage P
abbrev TlsM (P E H Error A : Type) := EStateM (TlsExecutionError Error) (TlsExecutionState P E H) A
structure TlsDestructorQueries (P E H Error : Type) where
  /-- Actual target/machine layout cache, never inferred from a target triple. -/
  unitPtrMut : TyAndLayout MIR.TyId
  unitPtrConst : TyAndLayout MIR.TyId
  u32Layout : TyAndLayout MIR.TyId
  lookupLinkSection : String → TlsM P E H Error (Array (TlsImmediate P × MIR.SpanRef))
  getPointerFnInstance : Pointer (Option P) → TlsM P E H Error CallInstance
  evalWindows : String → String → TlsM P E H Error (Scalar P)
  /-- Source call_thread_root_function: ABI checks, real frames, arguments,
  no return destination, ReturnContinuation::Stop { cleanup: true },
  empty-stack/origin-span checks, source span, and call errors are mandatory. -/
  callThreadRootFunction : CallInstance → TlsCallAbi → Array (OpTy P) → MIR.SpanRef → TlsM P E H Error Unit

private def setStage (stage : TlsDtorsStage P) : TlsM P E H Error Unit := do
  let state ← EStateM.get
  EStateM.set { state with stage := stage }
private def argument (scalar : Scalar P) (layout : TyAndLayout MIR.TyId) : OpTy P :=
  ⟨.immediate (.scalar scalar),layout⟩
private def pointerScalar (target : RuntimeTargetDataLayout) (pointer : Pointer (Option P)) : TlsM P E H Error (Scalar P) :=
  match Scalar.fromMaybePointer target.base pointer with
  | .ok scalar => pure scalar
  | .error error => throw (.scalar error)

private def schedulePthread (target : RuntimeTargetDataLayout) (queries : TlsDestructorQueries P E H Error)
    (lastKey : Option TlsKey) : TlsM P E H Error StackEmptyCallbackResult := do
  let state ← EStateM.get
  let thread := state.exit.tls.manager.activeThread
  let (found,data) := state.data.fetchDestructor lastKey thread
  let (found,data) := if found.isSome then (found,data) else data.fetchDestructor none thread
  EStateM.set { state with data := data }
  match found with
  | none => pure .Ready
  | some (destructor,pointer,key) =>
    setStage (.pthread (some key))
    unless pointer.offset.bytes != 0 do throw (.tls .nullDestructorData)
    let scalar ← pointerScalar target pointer
    queries.callThreadRootFunction destructor.fnInstance .cNoUnwind
      #[argument scalar queries.unitPtrMut] destructor.span
    pure .Pending

private def scheduleAtexit (queries : TlsDestructorQueries P E H Error) : TlsM P E H Error StackEmptyCallbackResult := do
  let state ← EStateM.get
  let (found,data) := state.data.popThreadAtexit state.exit.tls.manager.activeThread
  EStateM.set { state with data := data }
  match found with
  | none => pure .Ready
  | some destructor =>
    queries.callThreadRootFunction destructor.fnInstance .cNoUnwind
      #[argument destructor.data queries.unitPtrMut] destructor.span
    pure .Pending

/-- Source Windows FLS clears the previous value after return, not before call;
keys registered after the initial snapshot are not appended to this worklist. -/
private def scheduleWindowsFls (target : RuntimeTargetDataLayout) (queries : TlsDestructorQueries P E H Error)
    (lastKey : Option TlsKey) (remaining : List TlsKey)
    (callbacks : Array (TlsImmediate P × MIR.SpanRef)) : TlsM P E H Error StackEmptyCallbackResult := do
  let state ← EStateM.get
  let thread := state.exit.tls.manager.activeThread
  let data := match lastKey with
    | none => state.data
    | some key => { state.data with keys := state.data.keys.map fun entry =>
        if entry.key == key then { entry with data := entry.data.filter (·.1 != thread) } else entry }
  EStateM.set { state with data := data, stage := .windows none remaining callbacks }
  let mut remaining := remaining
  while !remaining.isEmpty do
    let key := remaining.head!
    remaining := remaining.tail!
    setStage (.windows none remaining callbacks)
    let state ← EStateM.get
    if let some entry := state.data.keys.find? (·.key == key) then
      if let some destructor := entry.destructor then
        if let some (_,pointer) := entry.data.find? (·.1 == thread) then
          unless pointer.offset.bytes != 0 do throw (.tls .nullDestructorData)
          setStage (.windows (some key) remaining callbacks)
          let scalar ← pointerScalar target pointer
          queries.callThreadRootFunction destructor.fnInstance .systemNoUnwind
            #[argument scalar queries.unitPtrMut] destructor.span
          return .Pending
  pure .Ready

private def scheduleWindowsCallback [PointerProvenance P] (target : RuntimeTargetDataLayout)
    (queries : TlsDestructorQueries P E H Error) (destructor : TlsImmediate P) (span : MIR.SpanRef) : TlsM P E H Error Unit := do
  let scalar ← match destructor.value.toScalar with
    | .ok scalar => pure scalar
    | .error error => throw (.immediate error)
  let pointer ← match scalar.toPointer target.base with
    | .ok pointer => pure pointer
    | .error error => throw (.scalar error)
  let fnInstance ← queries.getPointerFnInstance pointer
  let reason ← queries.evalWindows "c" "DLL_THREAD_DETACH"
  let null ← match Scalar.nullPointer target.base with
    | .ok scalar => pure scalar
    | .error error => throw (.scalar error)
  queries.callThreadRootFunction fnInstance .systemNoUnwind
    #[argument null queries.unitPtrConst, argument reason queries.u32Layout, argument null queries.unitPtrConst] span

/-- One source on_stack_empty callback invocation. Stage changes which precede
calls and mutations remain on errors; transitions after a failed lookup/call
are not performed. There is no fuel cutoff for pthread destructor rounds. -/
def tlsOnStackEmpty [PointerProvenance P] (platform : TlsPlatform) (target : RuntimeTargetDataLayout)
    (queries : TlsDestructorQueries P E H Error) : TlsM P E H Error StackEmptyCallbackResult := do
  let state ← EStateM.get
  match state.stage with
  | .init =>
    setStage (if platform.unix then .pthread none else .afterPthread)
    pure .Pending
  | .initForExit =>
    if platform.unix then
      let roots := state.data.leakAllThreadTls state.exit.tls.manager.activeThread state.exit.staticRoots
      EStateM.set { state with exit := { state.exit with staticRoots := roots } }
    setStage .afterPthread
    pure .Pending
  | .pthread key =>
    match ← schedulePthread target queries key with
    | .Pending => pure .Pending
    | .Ready => setStage .afterPthread; pure .Pending
  | .afterPthread =>
    match platform.os with
    | .linux | .macos => setStage .threadAtexit
    | .windows =>
      let callbacks ← queries.lookupLinkSection ".CRT$XLB"
      let after ← EStateM.get
      -- The source BTreeMap's ascending numeric key order is explicit.
      let keys := (after.data.keys.filter (·.destructor.isSome)).map (·.key)
      let keys := keys.toList.mergeSort (fun a b => a.toNat ≤ b.toNat)
      setStage (.windows none keys callbacks)
    | .other _ => setStage .done
    pure .Pending
  | .threadAtexit =>
    match ← scheduleAtexit queries with
    | .Pending => pure .Pending
    | .Ready => setStage .done; pure .Pending
  | .windows lastKey remaining callbacks =>
    match ← scheduleWindowsFls target queries lastKey remaining callbacks with
    | .Pending => pure .Pending
    | .Ready =>
      -- FLS state may have changed while clearing/skipping keys.
      let after ← EStateM.get
      match after.stage with
      | .windows last remaining callbacks =>
        match callbacks.back? with
        | none => setStage .done; pure .Pending
        | some (destructor,span) =>
          setStage (.windows last remaining callbacks.pop)
          scheduleWindowsCallback target queries destructor span
          pure .Pending
      | _ => throw (.tls .destructorsRemain)
  | .done =>
    let result := state.data.deleteAllThreadTls state.exit.tls.manager.activeThread
    match result with
    | .ok () data => EStateM.set { state with data := data }; pure .Ready
    | .error error data => EStateM.set { state with data := data }; throw (.tls error)

def finishThreadOnStackEmpty [PointerProvenance P] (platform : TlsPlatform) (target : RuntimeTargetDataLayout)
    (destructors : TlsDestructorQueries P E H Error) (exit : ThreadExitQueries P E H ProvExtra Error) : TlsM P E H Error StackEmptyCallbackResult := do
  match ← tlsOnStackEmpty platform target destructors with
  | .Pending => pure .Pending
  | .Ready =>
    let state ← EStateM.get
    match terminateActiveThread exit false state.exit with
    | .ok () next => EStateM.set { state with exit := next }; pure .Ready
    | .error error next => EStateM.set { state with exit := next }; throw (.exit error)

end Miri.Interpreter
