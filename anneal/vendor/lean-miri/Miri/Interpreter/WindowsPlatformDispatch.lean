import Miri.Interpreter.WindowsPlatformMachine
import Miri.Interpreter.ForeignItems

namespace Miri.Interpreter.WindowsPlatformDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | heapAlloc | heapFree | heapRealloc | localFree | setError | getError | ntStatus
  | systemInfo | commandLine | timer | symbol | exitProcess | console | moduleName | formatMessage | unwind
  deriving DecidableEq, Repr
inductive ArgType where | pointer | handle | usize | u32 | bool | i32 | unit | module | farproc | localHandle | unwindReason
  deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType
def parse : String → Option Operation
  | "HeapAlloc" => some .heapAlloc | "HeapFree" => some .heapFree | "HeapReAlloc" => some .heapRealloc
  | "LocalFree" => some .localFree | "SetLastError" => some .setError | "GetLastError" => some .getError
  | "RtlNtStatusToDosError" => some .ntStatus | "GetSystemInfo" => some .systemInfo
  | "GetCommandLineW" => some .commandLine | "CreateWaitableTimerExW" => some .timer
  | "GetProcAddress" => some .symbol | "ExitProcess" => some .exitProcess
  | "GetConsoleScreenBufferInfo" => some .console | "GetModuleFileNameW" => some .moduleName
  | "FormatMessageW" => some .formatMessage | "_Unwind_RaiseException" => some .unwind | _ => none

def signature : Operation → Signature
  | .heapAlloc => ⟨#[.handle,.u32,.usize],.pointer⟩
  | .heapFree => ⟨#[.handle,.u32,.pointer],.bool⟩
  | .heapRealloc => ⟨#[.handle,.u32,.pointer,.usize],.pointer⟩
  | .localFree => ⟨#[.localHandle],.localHandle⟩
  | .setError | .exitProcess => ⟨#[.u32],.unit⟩
  | .getError => ⟨#[],.u32⟩ | .ntStatus => ⟨#[.i32],.u32⟩
  | .systemInfo => ⟨#[.pointer],.unit⟩ | .commandLine => ⟨#[],.pointer⟩
  | .timer => ⟨#[.pointer,.pointer,.u32,.u32],.handle⟩
  | .symbol => ⟨#[.module,.pointer],.farproc⟩
  | .console => ⟨#[.handle,.pointer],.bool⟩
  | .moduleName => ⟨#[.module,.pointer,.u32],.u32⟩
  | .unwind => ⟨#[.pointer],.unwindReason⟩
  | .formatMessage => ⟨#[.u32,.pointer,.u32,.u32,.pointer,.u32,.pointer],.u32⟩
structure Hooks (S O E K F : Type) where
  platform : WindowsPlatform.Hooks S O E K F
  systemConvention : M S CanonAbi
  /-- The exact shim symbol is part of the compiler query identity. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  /-- Replace active stack with ProgramExitHandler(ExitCalled), not normal return. -/
  startExit : Int32 → M S Unit
  targetEnv : String
  handleStartUnwind : OpTy Provenance → M S Unit
private def checked (h : Hooks S O E K F) (operation : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let signature := signature operation
  let callee ← h.expectedAbi name signature
  if callee.conv != (← if operation == .unwind then pure .C else h.systemConvention) || callee.cVariadic || callee.args.size != signature.args.size ||
      callee.fixedCount.toNat != signature.args.size then throw (.invalidProgram "compiler Windows platform signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Windows platform calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Windows platform variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Windows platform argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Windows platform return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "Windows platform argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != signature.args.size then throw (.invalidProgram "Windows platform operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler Windows platform ABI argument missing")
    h.transmute op expected.layout
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked Windows platform argument missing")

def dispatch (h : Hooks S O E K F) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  if operation == .unwind && h.targetEnv != "gnu" then
    throw (.unsupported "_Unwind_RaiseException requires MinGW Windows")
  let args ← checked h operation name abi args
  let p := h.platform
  match operation with
  | .unwind =>
    h.handleStartUnwind (← arg args 0)
    return .NeedsUnwind
  | .heapAlloc => h.writePointer (← WindowsPlatform.heapAlloc p (← arg args 0) (← arg args 1) (← arg args 2)) dest
  | .heapFree => WindowsPlatform.heapFree p (← arg args 0) (← arg args 1) (← arg args 2); h.writeInt 1 dest
  | .heapRealloc => h.writePointer (← WindowsPlatform.heapRealloc p (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3)) dest
  | .localFree => WindowsPlatform.localFree p (← arg args 0); h.writePointer p.nullPointer dest
  | .setError => IoError.setLastError p.environment.errors (.raw (← p.readScalar (← arg args 0)))
  | .getError => h.writeScalar (← IoError.getLastError p.environment.errors) dest
  | .ntStatus => h.writeInt (Int.ofNat (WindowsPlatform.ntStatusToDos (← p.environment.readU32 (← arg args 0))).toNat) dest
  | .systemInfo => WindowsPlatform.systemInfo p (← arg args 0)
  | .commandLine =>
    let some pointer ← p.commandLine | throw (.invalidProgram "command line requires initialized machine")
    h.writePointer pointer dest
  | .timer =>
    WindowsPlatform.timer p (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3)
    h.writePointer p.nullPointer dest
  | .symbol => h.writePointer (← WindowsPlatform.getProcAddress p (← arg args 0) (← arg args 1)) dest
  | .exitProcess =>
    let scalar ← p.readScalar (← arg args 0)
    let code ← match scalar.toInt32 with
      | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
    h.startExit code
    return .AlreadyJumped
  | .console =>
    let _ ← p.environment.readIsize (← arg args 0)
    p.derefPointer (← arg args 1)
    h.writeInt 0 dest
  | .moduleName => WindowsPlatform.moduleFileName p (← arg args 0) (← arg args 1) (← arg args 2) dest
  | .formatMessage =>
    let length ← WindowsPlatform.formatMessage p (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4) (← arg args 5) (← arg args 6)
    h.writeInt (Int.ofNat length.toNat) dest
  return .NeedsReturn

def bindWindows (h : Hooks S O E K F)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst := {
  base with windows := fun name abi args dest => do
    if base.family != .windows then throw (.invalidProgram "Windows platform dispatcher on non-Windows target")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.windows name abi args dest }
/-- Bind the actual unwind payload stack; this stores payloads and leaves
control transfer to the returned NeedsUnwind, exactly as the source. -/
def bindUnwind (unwind : Unwind.Hooks K U C Other) (choice : C)
    (base : Hooks (MachineHooks.State K U) O E Kind F) :
    Hooks (MachineHooks.State K U) O E Kind F := {
  base with handleStartUnwind := Unwind.handleStartUnwind unwind choice }
end Miri.Interpreter.WindowsPlatformDispatch
