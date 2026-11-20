import Miri.Interpreter.Native.Trace

/-! Resumable source supervisor and child-side FFI protocol. A finite prefix
ending in a wait is pending execution, never a completed successful call. -/
namespace Miri.Interpreter.Native.Trace
open Miri.ABI Miri.Memory Miri.MIR
inductive Phase where
  | initialStop
  | listen
  | startStop
  | faultOff (pid : Pid) (prep : FaultPreparation)
  | faultStep (pid : Pid) (prep : FaultPreparation)
  | faultOn (pid : Pid) (saved : Registers)
  | died (code : Option Int32)
  deriving Repr
structure Runtime where
  supervisor : Supervisor
  phase : Phase := .initialStop
  deriving Repr
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def require (ok : Bool) (message : String) : RvalueM S Unit :=
  unless ok do invalid message

/-- One supervisor transition, preserving source ptrace/signal ordering across
explicit pending waits. In particular protection is restored before resumption. -/
def advance (h : Hooks S C) (choice : C) (runtime : Runtime) : RvalueM S Runtime := do
  let sv := runtime.supervisor
  unless h.pageSize != 0 do invalid "native tracer page size sentinel"
  match runtime.phase with
  | .died _ => pure runtime
  | .initialStop =>
    match ← waitSignalStep h choice (some sv.currentPid) .stop with
    | .pending => pure runtime
    | .died code => pure { runtime with phase := .died code }
    | .ready _ =>
      require (← h.continueProcess choice sv.currentPid none) "initial ptrace continue failed"
      pure { runtime with phase := .listen }
  | .listen =>
    let (listener,event) ← poll h choice sv.listener
    let sv := { sv with listener }
    let runtime := { runtime with supervisor := sv }
    match event with
    | none => pure runtime
    | some (.died code) => pure { runtime with phase := .died code }
    | some (.start info) =>
      let sv := { sv with pages := info.pagePtrs, stack := some info.stackPtr }
      h.confirm choice
      pure { supervisor := sv, phase := .startStop }
    | some .endFfi =>
      h.sendEvents choice sv.events
      let sv := { sv with events := #[], stack := none }
      require (← h.continueProcess choice sv.currentPid none) "end FFI ptrace continue failed"
      pure { supervisor := sv, phase := .listen }
    | some (.syscall pid) =>
      require (← h.syscall choice pid) "ptrace syscall failed"
      pure runtime
    | some (.status pid signal) =>
      if signal == .segv then
        let some stack := sv.stack | invalid "segfault received without callback stack"
        match ← prepareFault h choice pid sv.pages stack sv.events with
        | none => pure { runtime with phase := .died none }
        | some prep =>
          require (← h.continueProcess choice pid none) "mempr_off continue failed"
          pure { supervisor := { sv with events := prep.events }, phase := .faultOff pid prep }
      else
        h.unexpectedSignal choice signal
        unless ← h.syscall choice pid do h.kill choice pid .cont
        pure runtime
  | .startStop =>
    match ← waitSignalStep h choice none .stop with
    | .pending => pure runtime
    | .died code => pure { runtime with phase := .died code }
    | .ready pid =>
      require (← h.syscall choice pid) "start FFI ptrace syscall failed"
      pure { supervisor := { sv with currentPid := pid }, phase := .listen }
  | .faultOff pid prep =>
    match ← waitSignalStep h choice (some pid) .stop with
    | .pending => pure runtime
    | .died code => pure { runtime with phase := .died code }
    | .ready _ =>
      h.setRegisters choice pid prep.saved
      h.singleStep choice pid
      pure { runtime with phase := .faultStep pid prep }
  | .faultStep pid _ =>
    -- Exactly one wait, without wait_for_signal's automatic continuation.
    match ← h.wait choice (some pid) false with
    | .error _ => pure { runtime with phase := .died none }
    | .ok status =>
      match status with
      | .signaled _ signal | .stopped _ signal | .ptraceEvent _ signal =>
        if signal == .segv then invalid "native code segfaulted when re-trying memory access; native callback into Rust?"
      | _ => pure ()
      let some stack := sv.stack | invalid "native callback stack unavailable"
      clearCallbackStack h choice pid stack
      let saved ← h.registers choice pid
      h.setRegisters choice pid { saved with ip := h.memprOn, sp := stack+512 }
      require (← h.continueProcess choice pid none) "mempr_on continue failed"
      pure { runtime with phase := .faultOn pid saved }
  | .faultOn pid saved =>
    match ← waitSignalStep h choice (some pid) .stop with
    | .pending => pure runtime
    | .died code => pure { runtime with phase := .died code }
    | .ready _ =>
      h.setRegisters choice pid saved
      require (← h.syscall choice pid) "fault completion ptrace syscall failed"
      pure { runtime with phase := .listen }

structure ChildHooks (S C : Type) where
  hostBits : Nat
  pageSize : Nat
  lock : C → RvalueM S Unit
  unlock : C → RvalueM S Unit
  enabled : S → Bool
  /-- Actual isolated allocator pages, in source enumeration order. -/
  pages : C → RvalueM S (Array (Nat × Nat))
  allocateStack : C → Nat → RvalueM S Nat
  freeStack : C → Nat → RvalueM S Unit
  send : C → TraceRequest → RvalueM S Unit
  receiveConfirmation : C → RvalueM S Unit
  raise : C → Signal → RvalueM S Unit
  protect : C → Nat → Nat → Bool → RvalueM S Unit
  /-- Source timeout is 5 seconds; timeout panics, IPC disconnect returns none. -/
  receiveEvents : C → Nat → RvalueM S (Except Bool (Array AccessEvent))
  setInterchange : C → Nat → RvalueM S Unit
  currentContextAddress : C → RvalueM S Nat

private def checkedHost (h : ChildHooks S C) (n : Nat) : RvalueM S Nat :=
  if n < 2^h.hostBits then pure n else invalid "native child host usize arithmetic overflow"

/-- Caller must hold the shared supervisor mutex. Protected execution errors
abort the external process in Rust; they do not manufacture cleanup/success. -/
def doFfiLocked (h : ChildHooks S C) (choice : C) (action : RvalueM S A) :
    RvalueM S (A × Option (Array AccessEvent)) := do
  unless h.enabled (← get) do return (← action,none)
  let pages ← h.pages choice
  if h.pageSize == 0 then invalid "native isolated allocator page size zero"
  let mut pagePtrs := #[]
  for (base,size) in pages do
    for i in [:size/h.pageSize] do pagePtrs := pagePtrs.push (← checkedHost h (base+i*h.pageSize))
  let stack ← h.allocateStack choice 1024
  h.send choice (.startFfi ⟨pagePtrs,stack⟩)
  h.receiveConfirmation choice
  h.raise choice .stop
  for (base,size) in pages do h.protect choice base size false
  let value ← action
  for (base,size) in pages do h.protect choice base size true
  h.raise choice .usr1
  h.freeStack choice stack
  let events ← h.receiveEvents choice 5
  match events with
  | .ok events => pure (value,some events)
  | .error false => pure (value,none)
  | .error true => invalid "Waiting for accesses from supervisor timed out!"

/-- Source lock is acquired even with tracing disabled. A normal interpreter
error unlocks via the Rust mutex guard; a backend process abort has no successor. -/
def doFfi (h : ChildHooks S C) (choice : C) (action : RvalueM S A) :
    RvalueM S (A × Option (Array AccessEvent)) := do
  h.lock choice
  try
    let result ← doFfiLocked h choice action
    h.unlock choice
    pure result
  catch error =>
    h.unlock choice
    throw error

/-- Native InterpCx interchange is set outside the supervisor lock and cleared
only after its normal return. Callback aborts cannot return fabricated bytes. -/
def rawCall (h : ChildHooks S C) (choice : C) (action : RvalueM S A) :
    RvalueM S (A × Option (Array AccessEvent)) := do
  let address ← h.currentContextAddress choice
  h.setInterchange choice address
  let result ← doFfi h choice action
  h.setInterchange choice 0
  pure result

def registerRetcode (h : ChildHooks S C) (choice : C) (code : Int32) : RvalueM S Unit := do
  h.lock choice
  try
    if h.enabled (← get) then
      h.send choice (.overrideRetcode code)
      h.receiveConfirmation choice
    h.unlock choice
  catch error =>
    h.unlock choice
    throw error
end Miri.Interpreter.Native.Trace
