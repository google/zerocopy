import Miri.Interpreter.Clock
import Miri.Interpreter.ProvenanceGC
import Miri.Interpreter.Float

/-! Pinned machine.rs::before_terminator and thread.rs::maybe_preempt_active_thread.
Progress-report formatting is omitted. Random Bernoulli draws use the exact
rand 0.10.3 64-bit threshold support; choices below that threshold are
impossible even when the probability is positive. Full UB freedom must quantify
over every admitted choice, not just one executable invocation. -/
namespace Miri.Interpreter.TerminatorMachine
open Miri.ABI Miri.Memory
open MachineHooks (M)

structure Control (Host : Type) where
  basicBlockCount : UInt64
  sinceGc : UInt32
  gcInterval : UInt32
  monotonic : Clock.Monotonic Host
  preemptionRateBits : UInt64
  checkedArithmetic : Bool

structure Hooks (K User Host : Type) where
  getControl : User → Control Host
  setControl : Control Host → User → User
  provenance : ProvenanceGC.Hooks K User
  /-- Actual blocking_io::run_gc (weak readiness/source-description cleanup).
  This required leaf must not be replaced with success if I/O is in use. -/
  blockingIoGc : M K User Unit

private def updateControl (h : Hooks K User Host) (f : Control Host → Control Host) : M K User Unit := do
  let state ← get
  let user := h.setControl (f (h.getControl state.machine.user)) state.machine.user
  set { state with machine := { state.machine with user } }

/-- Decoded binary64 from source MiriConfig, retaining signed zero. rand
0.10.3 Bernoulli::new converts p to floor(p * 2^64), then samples a u64 `v`
and returns `v < threshold`. Use its exact rational form so tiny probabilities
retain the source's empty-success support. Invalid probabilities trigger the
source random_bool invariant only if queried. -/
def permitsPreemption (rate : UInt64) (choice : Bool) : Except StepError Bool := do
  let decoded ← ((FloatBits.mk .binary64 (BitVec.ofNat 128 rate.toNat)).decode).mapError
    (fun error => .invalidProgram s!"preemption probability encoding: {reprStr error}")
  let .finite numerator denominator := decoded.value |
    throw (.invalidProgram "nonfinite random_bool probability")
  if denominator == 0 || numerator > denominator || (decoded.negative && numerator != 0) then
    throw (.invalidProgram "random_bool probability outside [0,1]")
  let threshold := numerator * 2^64 / denominator
  return if choice then threshold > 0 else threshold < 2^64

/-- A choice outside the configured support is unresolved input, never Rust
UB or a successful skipped preemption. Fixed scheduling never queries it. -/
def maybePreemptWithChoice (h : Hooks K User Host) (draw : M K User Bool) : M K User Unit := do
  unless (← get).machine.threads.fixedScheduling do
    let control := h.getControl (← get).machine.user
    let choice ← draw
    let allowed ← match permitsPreemption control.preemptionRateBits choice with
      | .ok allowed => pure allowed
      | .error error => throw error
    unless allowed do throw (.invalidProgram "preemption choice outside configured support")
    if choice then
      modify fun state => { state with machine := { state.machine with threads :=
        state.machine.threads.yield } }

def beforeTerminatorWithChoice [DecidableEq K] (h : Hooks K User Host) (preempt : M K User Bool) : M K User Unit := do
  let control := h.getControl (← get).machine.user
  if control.checkedArithmetic && control.basicBlockCount.toNat + 1 ≥ 2^64 then
    throw (.invalidProgram "basic_block_count arithmetic overflow")
  updateControl h (fun control => { control with basicBlockCount := control.basicBlockCount + 1 })
  let control := h.getControl (← get).machine.user
  if control.checkedArithmetic && control.sinceGc.toNat + 1 ≥ 2^32 then
    throw (.invalidProgram "since_gc arithmetic overflow")
  updateControl h (fun control => { control with sinceGc := control.sinceGc + 1 })
  let control := h.getControl (← get).machine.user
  if control.gcInterval > 0 && control.sinceGc >= control.gcInterval then
    updateControl h (fun control => { control with sinceGc := 0 })
    ProvenanceGC.run h.provenance
    h.blockingIoGc
  maybePreemptWithChoice h preempt
  let control := h.getControl (← get).machine.user
  let clock ← match control.monotonic.tick control.checkedArithmetic with
    | .ok clock => pure clock
    | .error error => throw error
  updateControl h (fun control => { control with monotonic := clock })

/-- Retain the explicit-value APIs as source-equivalent deterministic wrappers. -/
def maybePreempt (h : Hooks K User Host) (choice : Bool) : M K User Unit :=
  maybePreemptWithChoice h (pure choice)
def beforeTerminator [DecidableEq K] (h : Hooks K User Host) (preempt : Bool) : M K User Unit :=
  beforeTerminatorWithChoice h (pure preempt)

/-- Install this source implementation into the same small-step driver. -/
def bindStep [DecidableEq K]
    (base : StepHooks Provenance LocalLayout MachineHooks.FrameExtra (MachineHooks.MachineState K User) C V)
    (h : Hooks K User Host) (preemptionChoice : C → Bool) :
    StepHooks Provenance LocalLayout MachineHooks.FrameExtra (MachineHooks.MachineState K User) C V :=
  { base with beforeTerminator := fun choice state =>
    match (beforeTerminator h (preemptionChoice choice)).run state with
    | .ok value state => (state,.ok value)
    | .error error state => (state,.error error) }

end Miri.Interpreter.TerminatorMachine

namespace Miri.Interpreter.TerminatorMachine
 theorem updateControl_eq (h : Hooks K User Host) (f : Control Host → Control Host)
    (state : MachineHooks.State K User) :
    updateControl h f state = .ok () {state with machine := {state.machine with
      user := h.setControl (f (h.getControl state.machine.user)) state.machine.user}} := by rfl
end Miri.Interpreter.TerminatorMachine
