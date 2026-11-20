import Miri.Interpreter.Native.Types

/-! Rust supervisor protocol and Capstone result interpretation. External decode,
ptrace, IPC, host signal, and page-protection effects are explicit operations;
there is no assumption that an arbitrary native execution is safe. -/
namespace Miri.Interpreter.Native.Trace
open Miri.ABI Miri.Memory Miri.MIR
abbrev Pid := Int32
inductive Signal where
  | stop | usr1 | segv | cont | other (number : Int32)
  deriving DecidableEq, Repr
inductive WaitStatus where
  | exited (pid : Pid) (code : Int32)
  | signaled (pid : Pid) (signal : Signal)
  | syscall (pid : Pid)
  | stopped (pid : Pid) (signal : Signal)
  | ptraceEvent (pid : Pid) (signal : Signal)
  | other
  deriving Repr
inductive ExecEvent where
  | start (info : StartFfiInfo)
  | endFfi
  | status (pid : Pid) (signal : Signal)
  | syscall (pid : Pid)
  | died (code : Option Int32)
  deriving Repr
structure Listener where
  attached : Bool := false
  overrideRetcode : Option Int32 := none
  lastCode : Option Int32 := none
  deriving Repr
structure Supervisor where
  listener : Listener := {}
  currentPid : Pid
  pages : Array Nat := #[]
  stack : Option Nat := none
  events : Array AccessEvent := #[]
  deriving Repr
structure Registers where
  /-- Full backend register image, not just IP/SP; restoration preserves all regs. -/
  image : Array UInt8
  ip : Nat
  sp : Nat
  deriving Repr
structure Operand where
  isMemory : Bool
  size : UInt8
  access : Option (Bool × Bool)
  deriving Repr
structure Hooks (S C : Type) where
  hostBits : Nat
  wordSize : Nat
  pageSize : Nat
  /-- Failure models waitid error; none is WNOHANG/StillAlive. -/
  wait : C → Option Pid → Bool → RvalueM S (Except Unit WaitStatus)
  pollRequest : C → RvalueM S (Option TraceRequest)
  confirm : C → RvalueM S Unit
  continueProcess : C → Pid → Option Signal → RvalueM S Bool
  syscall : C → Pid → RvalueM S Bool
  kill : C → Pid → Signal → RvalueM S Unit
  yieldHost : C → RvalueM S Unit
  sendEvents : C → Array AccessEvent → RvalueM S Unit
  signalAddress : C → Pid → RvalueM S Nat
  registers : C → Pid → RvalueM S Registers
  setRegisters : C → Pid → Registers → RvalueM S Unit
  writeWord : C → Pid → Nat → Nat → RvalueM S Unit
  /-- ptrace read errors are source-defaulted to zero, represented by none. -/
  readWord : C → Pid → Nat → RvalueM S (Option (Array UInt8))
  decodeOne : C → Array UInt8 → Nat → RvalueM S (Array Operand)
  singleStep : C → Pid → RvalueM S Unit
  memprOff : Nat
  memprOn : Nat
  pageAddrGlobal : Nat
  pageCountGlobal : Nat
  unexpectedSignal : C → Signal → RvalueM S Unit
  segfaultDiagnostic : C → Nat → Array Nat → Registers → RvalueM S Unit

private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def checked (h : Hooks S C) (value : Nat) : RvalueM S Nat :=
  if value < 2^h.hostBits then pure value else invalid "native trace host usize overflow"
private def require (ok : Bool) (message : String) : RvalueM S Unit :=
  unless ok do invalid message

/-- One listener polling iteration. None requests the source host yield/retry;
no bounded polling result is interpreted as process completion. -/
def poll (h : Hooks S C) (choice : C) (listener : Listener) :
    RvalueM S (Listener × Option ExecEvent) := do
  let mut listener := listener
  match ← h.wait choice none true with
  | .error _ => return (listener,some (.died (listener.overrideRetcode.or listener.lastCode)))
  | .ok status =>
    match status with
    | .exited _ code => listener := { listener with lastCode := some code }
    | .signaled .. => listener := { listener with lastCode := none }
    | .syscall pid =>
      if listener.attached then return (listener,some (.syscall pid))
    | .stopped pid signal | .ptraceEvent pid signal =>
      if listener.attached then
        if signal == .usr1 then return ({ listener with attached := false },some .endFfi)
        else return (listener,some (.status pid signal))
      else require (← h.continueProcess choice pid (some signal)) "ptrace continue failed"
    | .other => pure ()
  if let some request ← h.pollRequest choice then
    match request with
    | .startFfi info =>
      if listener.attached then invalid "Attempting to begin FFI multiple times!"
      return ({ listener with attached := true },some (.start info))
    | .overrideRetcode code =>
      listener := { listener with overrideRetcode := some code }
      h.confirm choice
  h.yieldHost choice
  pure (listener,none)

/-- Capstone memory operands retain read-before-write, uncertain RW writes, and
source partial event append before detecting a second memory operand. -/
def appendDecoded (addr : Nat) (operands : Array Operand)
    (initial : Array AccessEvent) : Except (StepError × Array AccessEvent) (Array AccessEvent) := do
  let mut events := initial
  let mut found := false
  for op in operands do
    if op.isMemory then
      let some (read,write) := op.access
        | throw (.invalidProgram "Capstone memory operand lacks access type",events)
      let range := AccessRange.mk addr op.size.toNat
      if read then events := events.push (.read range)
      if write then events := events.push (.write range (!read))
      if found then throw (.invalidProgram "more than one memory operand found",events)
      found := true
  pure events

inductive WaitResult where
  | ready (pid : Pid)
  | pending
  | died (code : Option Int32)
  deriving Repr
/-- One iteration of source wait_for_signal, retaining unknown-status continue
and signal forwarding. Caller retains pending state until the requested signal. -/
def waitSignalStep (h : Hooks S C) (choice : C) (pid : Option Pid)
    (signal : Signal) : RvalueM S WaitResult := do
  match ← h.wait choice pid false with
  | .error _ => pure (.died none)
  | .ok (.exited _ code) => pure (.died (some code))
  | .ok (.signaled ..) => pure (.died none)
  | .ok (.stopped actual got) | .ok (.ptraceEvent actual got) =>
    if got == signal then pure (.ready actual)
    else
      if ← h.continueProcess choice actual (some got) then pure .pending else pure (.died none)
  | .ok _ =>
    let some pid := pid | invalid "wait_for_signal unknown status without specific pid"
    require (← h.continueProcess choice pid none) "ptrace continue failed"
    pure .pending

/-- Bounded operational prefix of a possibly diverging wait. Exhaustion returns
pending; it never authorizes the caller to advance the supervisor protocol. -/
def waitSignal (h : Hooks S C) (choice : C) (pid : Option Pid)
    (signal : Signal) : Nat → RvalueM S WaitResult
  | 0 => pure .pending
  | fuel+1 => do
    match ← waitSignalStep h choice pid signal with
    | .pending => waitSignal h choice pid signal fuel
    | result => pure result

/-- Source instruction-byte collection reads ceil(15/wordSize) complete words,
with individual ptrace failures zero-filled before the Capstone call. -/
def instructionBytes (h : Hooks S C) (choice : C) (pid : Pid) (ip : Nat) : RvalueM S (Array UInt8) := do
  unless h.wordSize == 4 || h.wordSize == 8 do invalid "native tracer requires x86 host word size"
  let mut bytes := #[]
  for i in [:(15+h.wordSize-1)/h.wordSize] do
    let address ← checked h (ip+h.wordSize*i)
    let word ← h.readWord choice pid address
    let word := word.getD (Array.replicate h.wordSize (0 : UInt8))
    unless word.size == h.wordSize do invalid "ptrace read returned incorrect native word size"
    bytes := bytes ++ word
  pure bytes

def clearCallbackStack (h : Hooks S C) (choice : C) (pid : Pid) (stack : Nat) : RvalueM S Unit := do
  unless h.wordSize == 4 || h.wordSize == 8 do invalid "native tracer requires x86 host word size"
  let _ ← checked h (stack+1024)
  for i in [:1024/h.wordSize] do h.writeWord choice pid (stack+i*h.wordSize) 0

structure FaultPreparation where
  saved : Registers
  callback : Registers
  pageAddress : Nat
  pageCount : Nat
  bytes : Array UInt8
  events : Array AccessEvent
  deriving Repr

/-- Pure Rust-side preparation before mempr_off. Native faults outside the owned
pages kill the child; they never become a successful unknown memory access. -/
def prepareFault (h : Hooks S C) (choice : C) (pid : Pid) (pages : Array Nat)
    (stack : Nat) (events : Array AccessEvent) : RvalueM S (Option FaultPreparation) := do
  let addr ← h.signalAddress choice pid
  if h.pageSize == 0 then invalid "native tracer page size sentinel"
  let pageAddr := addr-addr%h.pageSize
  let mut owned := false
  for page in pages do
    let endAddr ← checked h (page+h.pageSize)
    if page <= addr && addr < endAddr then owned := true
  unless owned do
    let regs ← h.registers choice pid
    h.segfaultDiagnostic choice addr pages regs
    h.kill choice pid (.other 9)
    return none
  clearCallbackStack h choice pid stack
  let stackPtr ← checked h (stack+512)
  let saved ← h.registers choice pid
  let bytes ← instructionBytes h choice pid saved.ip
  let operands ← h.decodeOne choice bytes 0x1000
  let events ← match appendDecoded addr operands events with
    | .ok events => pure events
    | .error (error,_) => throw error
  let callback := { saved with ip := h.memprOff, sp := stackPtr }
  h.writeWord choice pid h.pageAddrGlobal pageAddr
  let nextPage ← checked h (pageAddr+h.pageSize)
  let count := if pages.contains nextPage then 2 else 1
  h.writeWord choice pid h.pageCountGlobal count
  h.setRegisters choice pid callback
  pure (some ⟨saved,callback,pageAddr,count,bytes,events⟩)
end Miri.Interpreter.Native.Trace
