import Miri.Interpreter.ExecutionChoices
import Miri.Interpreter.Math.Bindings
import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.ThreadStacks
import Miri.Interpreter.ThreadMachine

/-! Source-point choice dictionaries. Each callback consumes from the same
persistent tape, not a context-wide value reused at every callback invocation.
Compiler, physical memory, host operations retain their dictionaries. -/
namespace Miri.Interpreter.ExecutionChoiceBindings
open Miri.ABI Miri.Memory Miri.MIR
open ExecutionChoices

/-- Source IteratorRandom::choose then independent random sign flip. The
existing NaN relation enumerates [candidate,-candidate] pairs in source order;
these two events map to that relation without merging duplicate payloads. -/
def nanChoice (access : Access S) (candidates : List FloatBits) : RvalueM S Nat := do
  if candidates.isEmpty || candidates.length % 2 != 0 then
    throw (.invalidProgram "source NaN candidate/sign pair relation malformed")
  let selected ← index access .floatNaN (candidates.length/2)
  let flipped ← boolean access .floatSign
  pure (2*selected + if flipped then 1 else 0)

def floatHooks (access : Access S) (base : FloatOpsHooks P S C) : FloatOpsHooks P S C :=
  {base with chooseNaN := fun _ candidates => nanChoice access candidates}

/-- Source success_rate = 1.0 - failure_rate is a rounded binary64 subtraction,
not an exact rational complement. Preserve this distinction at endpoint rates. -/
def successRate (failure : UInt64) : Except StepError UInt64 := do
  let one := FloatBits.mk .binary64 (BitVec.ofNat 128 0x3ff0000000000000)
  let rate := FloatBits.mk .binary64 (BitVec.ofNat 128 failure.toNat)
  let success ← FloatBits.arithmetic .Sub one rate |>.mapError fun error => .invalidProgram s!"weak CAS rate: {reprStr error}"
  pure (UInt64.ofNat success.bits.toNat)

def atomicHooks (access : Access S) (failureRate : UInt64)
    (base : IntrinsicAtomicHooks P S C V) : IntrinsicAtomicHooks P S C V :=
  {base with
    loadChoiceRank := fun _ count => index access .atomicStale count
    weakPolicy := .mayFail
    weakSuccessChoice := fun _ => do
      let rate ← match successRate failureRate with
        | .ok rate => pure rate | .error error => throw error
      bernoulli access .weakCasSuccess rate}

private def equalRight (access : Access S) (enabled : Bool) : RvalueM S Bool := do
  if !enabled then return false
  pure (!(← boolean access .floatEqual))
private def fuse (access : Access S) (enabled : Bool) : RvalueM S Bool := do
  if !enabled then return false
  boolean access .floatFuse

def simdHooks (access : Access S) (base : IntrinsicSimdHooks P S C V) : IntrinsicSimdHooks P S C V :=
  {base with
    floatOps := floatHooks access base.floatOps
    chooseEqualFloatRight := fun _ _ _ => equalRight access base.floatOps.floatNondeterministic
    fuseMulAdd := fun _ => fuse access base.floatOps.floatNondeterministic}

def intrinsicHooks (access : Access S) (failureRate : UInt64)
    (base : IntrinsicHooks P S C V) : IntrinsicHooks P S C V :=
  {base with
    floatOps := floatHooks access base.floatOps
    atomicHooks := atomicHooks access failureRate base.atomicHooks
    simdHooks := simdHooks access base.simdHooks
    chooseEqualFloatRight := fun _ _ _ => equalRight access base.floatOps.floatNondeterministic
    fuseMulAdd := fun _ => fuse access base.floatOps.floatNondeterministic
    chooseStaticKnown := fun _ => boolean access .staticKnown}

def vtableHooks (access : Access S) (base : VTableHooks P S C F A) : VTableHooks P S C F A :=
  {base with globalSalt := fun _ => index access .globalSalt 32}

def mathHooks (access : Access S) (base : Math.Hooks P S C V) : Math.Hooks P S C V :=
  {base with
    floatOps := floatHooks access base.floatOps
    ulpError := fun _ bound => integer access .floatUlp (-Int.ofNat bound) (Int.ofNat bound)
    maxErrorPositive := fun _ => boolean access .floatSign
    relativeMagnitude := fun _ precision => index access .floatMagnitude (2^precision)
    relativeNegative := fun _ => boolean access .floatSign
    snanPowNaN := fun _ => boolean access .signalingPow}

def x86Hooks (access : Access S) (base : IntrinsicX86.Hooks P S C V) : IntrinsicX86.Hooks P S C V :=
  {base with
    architecture := {base.architecture with simd := simdHooks access base.architecture.simd}
    errorMagnitude := fun _ precision => index access .floatMagnitude (2^precision)
    errorNegative := fun _ => boolean access .floatSign}

def functionHooks (access : Access (MachineHooks.State K U))
    (base : FunctionPointers.Hooks K U Other) : FunctionPointers.Hooks K U Other :=
  {base with chooseSalt := do
    let selected ← index access .globalSalt 32
    if valid : selected < 32 then pure ⟨selected,valid⟩
    else throw (.invalidProgram "checked source global salt exceeded support")}

/-- Source scheduling never samples an empty iterator. Fixed scheduling skips
this callback in ThreadStacks.scheduleLocal; every enabled candidate is admitted. -/
def schedulerChoice (access : Access S) (candidates : List Miri.Concurrency.ThreadId) :
    RvalueM S (Option Miri.Concurrency.ThreadId) := do
  if candidates.isEmpty then return none
  let rank ← index access .scheduler candidates.length
  match candidates[rank]? with
  | some id => pure (some id)
  | none => throw (.invalidProgram "checked scheduling rank exceeded candidates")

def schedulerHooks (access : Access (ThreadStacks.State K U))
    (base : ThreadStacks.LocalSchedulerHooks K U) : ThreadStacks.LocalSchedulerHooks K U :=
  {base with choose := schedulerChoice access}

/-- Source thread creation may reuse a vector clock only from the exact safe
candidate set supplied by ThreadMachine. Consume one execution-tape
index at that point; empty support is never sampled, and out-of-range tape
inputs fail closed. The impossible post-index lookup remains a defensive
invalid-program error. Explicit reuse overrides are handled by ThreadMachine
before this hook is called. -/
def threadClockReuse {K U C O X F A Aff : Type}
    (access : Access (ThreadMachine.State K U))
    (base : ThreadMachine.Hooks K U C O X F A Aff) :
    ThreadMachine.Hooks K U C O X F A Aff :=
  {base with chooseReuseClock := fun candidates => do
    if candidates.isEmpty then return none
    let selected ← index access .threadClockReuse candidates.length
    match candidates[selected]? with
    | some clock => return some clock
    | none => throw (.invalidProgram "thread clock reuse choice exceeded safe candidates")}

/-- The tape request runs at the source post-GC preemption point, and only
outside fixed scheduling. Clock tick remains after the decision. -/
def beforeTerminator [DecidableEq K] (access : Access (MachineHooks.State K U))
    (h : TerminatorMachine.Hooks K U Host) : MachineHooks.M K U Unit :=
  TerminatorMachine.beforeTerminatorWithChoice h do
    let control := h.getControl (← get).machine.user
    bernoulli access .preemption control.preemptionRateBits
end Miri.Interpreter.ExecutionChoiceBindings
