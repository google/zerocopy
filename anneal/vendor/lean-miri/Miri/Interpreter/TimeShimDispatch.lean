import Miri.Interpreter.TimeShims
import Miri.Interpreter.ForeignItems

/-! Exact time entrypoints of Unix/macOS/Windows foreign-item dispatch. Mach
entrypoints deliberately keep pinned deprecated lenient ABI checking. -/
namespace Miri.Interpreter.TimeShimDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | gettimeofday | localtimeR | clockGettime | nanosleep | clockNanosleep
  | filetime | preciseFiletime | performanceCounter | performanceFrequency | sleep
  | machAbsolute | machTimebase | machWait
  deriving DecidableEq, Repr
inductive ShimType where
  | pointer | timevalPointer | timezonePointer | timeTPointer | tmPointer | timespecPointer
  | clockId | i32 | u32 | u64 | bool | unit
  deriving DecidableEq, Repr
structure Signature where
  systemAbi : Bool
  args : Array ShimType
  ret : ShimType
  deriving DecidableEq, Repr

def parse : String → Option Operation
  | "gettimeofday" => some .gettimeofday | "localtime_r" => some .localtimeR
  | "clock_gettime" => some .clockGettime | "nanosleep" => some .nanosleep
  | "clock_nanosleep" => some .clockNanosleep
  | "GetSystemTimeAsFileTime" => some .filetime
  | "GetSystemTimePreciseAsFileTime" => some .preciseFiletime
  | "QueryPerformanceCounter" => some .performanceCounter
  | "QueryPerformanceFrequency" => some .performanceFrequency
  | "Sleep" => some .sleep
  | "mach_absolute_time" => some .machAbsolute
  | "mach_timebase_info" => some .machTimebase
  | "mach_wait_until" => some .machWait
  | _ => none

def signature : Operation → Signature
  | .gettimeofday => ⟨false,#[.timevalPointer,.timezonePointer],.i32⟩
  | .localtimeR => ⟨false,#[.timeTPointer,.tmPointer],.tmPointer⟩
  | .clockGettime => ⟨false,#[.clockId,.timespecPointer],.i32⟩
  | .nanosleep => ⟨false,#[.pointer,.pointer],.i32⟩
  | .clockNanosleep => ⟨false,#[.clockId,.i32,.pointer,.pointer],.i32⟩
  | .filetime | .preciseFiletime => ⟨true,#[.pointer],.unit⟩
  | .performanceCounter | .performanceFrequency => ⟨true,#[.pointer],.bool⟩
  | .sleep => ⟨true,#[.u32],.unit⟩
  | .machAbsolute => ⟨false,#[],.u64⟩
  | .machTimebase => ⟨false,#[.pointer],.i32⟩
  | .machWait => ⟨false,#[.u64],.i32⟩
private def mach : Operation → Bool
  | .machAbsolute | .machTimebase | .machWait => true
  | _ => false
structure Hooks (S Host System TZ Timestamp : Type) where
  time : TimeShims.Hooks S Host System TZ Timestamp
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  systemConvention : M S CanonAbi
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
private def checked (h : Hooks S H Y Z T) (op : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let request := signature op
  if mach op then
    -- Pinned macOS uses check_shim_sig_deprecated: clash before convention,
    -- no argument/return type checking and no argument transmutation.
    h.checkSymbolClash name
    if caller.conv != .C then throw (.undefinedBehavior "Mach time calling convention mismatch")
    if caller.cVariadic then throw (.undefinedBehavior "Mach time caller signature is variadic")
    if args.size != request.args.size then throw (.undefinedBehavior "Mach time argument count mismatch")
    return args
  let callee ← h.expectedAbi name request
  let conv ← if request.systemAbi then h.systemConvention else pure CanonAbi.C
  if callee.conv != conv || callee.cVariadic || callee.args.size != request.args.size ||
      callee.fixedCount.toNat != request.args.size then throw (.invalidProgram "compiler time-shim signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "time-shim calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "time-shim variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "time-shim argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "time-shim return ABI mismatch")
  for (caller,callee) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat caller callee) then throw (.undefinedBehavior "time-shim argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != request.args.size then throw (.invalidProgram "time operands disagree with caller ABI")
  args.mapIdxM fun index operand => do
    let some expected := callee.args[index]? | throw (.invalidProgram "missing time-shim ABI argument")
    h.transmute operand expected.layout
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "missing checked time argument")

def dispatch (h : Hooks S H Y Z T) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  let request := signature operation
  -- Platform-specific name checks precede ABI checks as in source dispatch.
  if mach operation then
    if h.time.os != "macos" then return .NotSupported
  else if request.systemAbi then
    if h.time.family != .windows then return .NotSupported
  else if h.time.family != .unix then return .NotSupported
  if operation == .clockNanosleep then
    if !#["freebsd","linux","android","solaris","illumos"].contains h.time.os then
      throw (.unsupported "clock_nanosleep unavailable on this target OS")
  let args ← checked h operation name abi args
  let time := h.time
  let write := time.runtime.writeScalar
  match operation with
  | .gettimeofday => write (← TimeShims.gettimeofday time (← arg args 0) (← arg args 1)) dest
  | .localtimeR => time.writePointer (← TimeShims.localtimeR time (← arg args 0) (← arg args 1)) dest
  | .clockGettime => TimeShims.clockGettime time (← arg args 0) (← arg args 1) dest
  | .nanosleep => write (← TimeShims.nanosleep time (← arg args 0) (← arg args 1)) dest
  | .clockNanosleep => write (← TimeShims.clockNanosleep time (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3)) dest
  | .filetime | .preciseFiletime => TimeShims.getSystemTimeAsFileTime time name (← arg args 0)
  | .performanceCounter => write (← TimeShims.queryPerformanceCounter time (← arg args 0)) dest
  | .performanceFrequency => write (← TimeShims.queryPerformanceFrequency time (← arg args 0)) dest
  | .sleep => TimeShims.sleep time (← arg args 0)
  | .machAbsolute => time.writeInt (Int.ofNat (← TimeShims.machAbsoluteTime time).toNat) dest
  | .machTimebase => write (← TimeShims.machTimebaseInfo time (← arg args 0)) dest
  | .machWait => write (← TimeShims.machWaitUntil time (← arg args 0)) dest
  return .NeedsReturn

def bindForeign (h : Hooks S H Y Z T)
    (base : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) Ptr B I) :
    ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) Ptr B I := {
  base with
  unix := fun name abi args dest => do
    if base.family != h.time.family || base.os != h.time.os then throw (.invalidProgram "time-shim target mismatch")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest
  windows := fun name abi args dest => do
    if base.family != h.time.family || base.os != h.time.os then throw (.invalidProgram "time-shim target mismatch")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.windows name abi args dest }
end Miri.Interpreter.TimeShimDispatch
