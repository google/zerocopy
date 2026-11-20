import Miri.Interpreter.Native.Pipeline
import Miri.Interpreter.Native.Supervisor

/-! Initialization, callback construction, and mprotect helper boundaries from
native_lib/{mod.rs,trace/child.rs,trace/parent.rs,trace/stub.rs}. -/
namespace Miri.Interpreter.Native
open Miri.ABI Miri.Memory Miri.MIR
structure LibraryHooks (S C Handle : Type) where
  enabledBuild : Bool
  hostTriple : String
  targetTriple : String
  load : C → String → RvalueM S Handle
  allocateInterchange : C → Nat → RvalueM S Unit

/-- Source Machine::new checks host/target once per configured library, before
loading that library. Empty configuration does not spuriously reject a cross
compile, while the supported build still allocates its interchange cell. -/
def initializeLibraries (h : LibraryHooks S C Handle) (choice : C)
    (paths : Array String) : RvalueM S (Array (Handle × Library)) := do
  let mut libraries := #[]
  for path in paths do
    unless h.enabledBuild do
      throw (.invalidProgram "calling functions from native libraries via FFI is not supported in this build of Miri")
    unless h.hostTriple == h.targetTriple do
      throw (.invalidProgram "calling native C functions requires host and target to be the same")
    let handle ← h.load choice path
    libraries := libraries.push (handle,⟨path⟩)
  if h.enabledBuild then h.allocateInterchange choice 0
  pure libraries

inductive ForkResult where
  | parent (child : Trace.Pid)
  | child
  deriving Repr
inductive InitOutcome where
  | initialized
  | unavailable
  | supervisorExited (code : Int32)
  deriving Repr
structure InitHooks (S C : Type) where
  supported : Bool
  ptraceScope : C → RvalueM S (Option String)
  lock : C → RvalueM S Unit
  unlock : C → RvalueM S Unit
  initialized : S → Bool
  createChannels : C → RvalueM S Unit
  sysconfPageSize : C → RvalueM S Nat
  storePageSize : C → Nat → RvalueM S Unit
  fork : C → RvalueM S ForkResult
  /-- PTRACE_O_TRACESYSGOOD | TRACECLONE | TRACEFORK; false means seize failed. -/
  seize : C → Trace.Pid → Bool → Bool → Bool → RvalueM S Bool
  killChild : C → Trace.Pid → RvalueM S Unit
  /-- Actual supervisor operational execution. Returning means its source
  ExecEnd, not proof of completion/safety of the arbitrary native program. -/
  runSupervisor : C → Trace.Pid → RvalueM S (Option Int32)
  /-- Parent intentionally leaks the mutex guard before its supervisor loop. -/
  forgetGuard : C → RvalueM S Unit
  parentDeathSignal : C → Trace.Signal → RvalueM S Bool
  raise : C → Trace.Signal → RvalueM S Unit
  installSupervisor : C → RvalueM S Unit

/-- Ptrace-scope fast rejection precedes the initialized/lock check exactly as
source. Parent exit is explicit, not an initialized interpreter continuation. -/
def initSupervisor (h : InitHooks S C) (choice : C) : RvalueM S InitOutcome := do
  unless h.supported do return .unavailable
  if let some scope ← h.ptraceScope choice then
    if scope.toList.head? == some '3' then return .unavailable
  h.lock choice
  if h.initialized (← get) then
    h.unlock choice
    return .initialized
  h.createChannels choice
  let pageSize ← h.sysconfPageSize choice
  h.storePageSize choice pageSize
  match ← h.fork choice with
  | .parent child =>
    h.forgetGuard choice
    if ← h.seize choice child true true true then
      let code ← h.runSupervisor choice child
      pure (.supervisorExited (code.getD 1))
    else
      h.killChild choice child
      pure .unavailable
  | .child =>
    unless ← h.parentDeathSignal choice (.other 15) do
      throw (.invalidProgram "PR_SET_PDEATHSIG failed")
    h.raise choice .stop
    h.installSupervisor choice
    h.unlock choice
    pure .initialized

structure ClosureHooks (P S C V Code Closure : Type) where
  native : Hooks P S C V Code
  /-- Backend leaks descriptor data+closure until process exit, as source. -/
  build : C → Option (Array FfiType × FfiType) → Bool → RvalueM S Closure
  activeInterchange : S → Bool

/-- Unsupported signature conversion builds the source aborting closure with
an empty descriptor; it does not reject creation of the function pointer. -/
def buildClosure (h : ClosureHooks P S C V Code Closure) (choice : C) (fuel : Nat)
    (inputs : Array TyId) (output : TyId) : RvalueM S Closure := do
  let signature ← try
    let mut arguments := #[]
    for input in inputs do
      let layout ← queryLayout h.native choice input
      arguments := arguments.push (← ffiType h.native choice fuel layout)
    let resultLayout ← queryLayout h.native choice output
    let result ← ffiType h.native choice fuel resultLayout
    pure (some (arguments,result))
  catch error =>
    match error with
    | .unsupported _ => pure none
    | _ => throw error
  h.build choice signature signature.isNone

/-- Source callback always diagnoses and exits: successful native→Rust callbacks
are not implemented in pinned Miri either. The returned error has no value. -/
def callback (h : ClosureHooks P S C V Code Closure) (unsupportedSignature : Bool) : RvalueM S A := do
  unless h.activeInterchange (← get) do
    throw (.invalidProgram "libffi closure called while no FFI call is active")
  if unsupportedSignature then
    throw (.unsupported "calling a function pointer with unsupported argument/return type through the FFI boundary")
  throw (.unsupported "calling a function pointer through the FFI boundary")

structure ProtectionHooks (S C : Type) where
  hostBits : Nat
  pageAddress : S → Nat
  pageSize : S → Nat
  pageCount : S → Nat
  mprotect : C → Nat → Nat → Bool → RvalueM S Bool
  raiseStop : C → RvalueM S Bool
inductive ProtectionOutcome where
  | stopped
  | exit (code : Int32)
  deriving Repr
/-- Source off helper uses saturating multiplication, on helper wrapping
multiplication. Neither error unwinds through the synthetic callback stack. -/
def protectionHelper (h : ProtectionHooks S C) (choice : C) (off : Bool) : RvalueM S ProtectionOutcome := do
  let state ← get
  let product := h.pageSize state * h.pageCount state
  let bound := 2^h.hostBits
  let length := if off then min product (bound-1) else product % bound
  unless ← h.mprotect choice (h.pageAddress state) length off do return (.exit (-1))
  unless ← h.raiseStop choice do return (.exit (-1))
  pure .stopped
end Miri.Interpreter.Native
