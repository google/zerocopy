import Miri.Input.EvalCompilerMachine
import Miri.Interpreter.ExecutionCallTransport
import Miri.Interpreter.ExecutionSafety

/-! Source main/root calls and scheduled MIR steps share one physical execution
configuration. This is the connected runtime adapter, not a replacement for
constructing the remaining compiler/host leaves of ExecutionMachine.Config. -/
namespace Miri.Input.EvalExecutable
open Miri.ABI Miri.Memory Miri.Interpreter
open ExecutionStateTransport
abbrev W := EvalWorld.World
abbrev U Os R P H D O Aff B Host := ValidityMachine.UserState (W Os R P H D O Aff B Host)
abbrev Core Os R P H D O Aff B Host C ClockHost :=
  ExecutionMachine.Config MiriMemoryKind (Inner (W Os R P H D O Aff B Host)) C O ABI.ExternAbi ClockHost

/-- Main, constructors and TLS root calls receive the same fully assembled
call engine as MIR call terminators: real argument copies, FnEntry retags,
frame identities, return copies, protector release and cleanup are preserved. -/
def mainCalls (config : Core Os R P H D O Aff B Host C ClockHost) (limits : ExecutionMachine.Limits)
    (main : MainMachine.Hooks (U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi MIR.TyId) (ArgAbi MIR.TyId) Aff P) :
    MainMachine.Hooks (U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi MIR.TyId) (ArgAbi MIR.TyId) Aff P :=
  let functions := ExecutionCallTransport.functions
    (ExecutionCalls.helpers config.helpers (ExecutionMachine.callHooks config limits))
  let thread := {main.termination.tls.thread with functions}
  {main with
    functions := ExecutionCallTransport.pointers config.functions
    termination := {main.termination with tls := {main.termination.tls with thread}}}

/-- Runtime source choice events stay inside their actual dictionaries. A
configuration may depend on the current operation context, but no caller core
step replaces the existing interpreter: coreStep is fixed here. Main callback
capture, checked restore, actual termination and stack scheduling are mandatory. -/
def loop (configs : C → Core Os R P H D O Aff B Host C ClockHost) (limits : ExecutionMachine.Limits)
    (main : MainMachine.Hooks (U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi MIR.TyId) (ArgAbi MIR.TyId) Aff P)
    (base : RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind (U Os R P H D O Aff B Host)) :
    RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback :=
  let bound := MainMachine.bindLoop main base scheduler
  {bound with
    coreStep := fun choice => ExecutionStateTransport.step (configs choice) limits choice
    invokeStackEmptyCallback := fun choice callback state =>
      let h := mainCalls (configs choice) limits main
      MachineHooks.run (match callback with
        | .main _ => MainMachine.invoke h choice
        | .tls callback => ThreadLoops.invoke h.termination.tls choice callback) state}

/-- Fallible source configuration loop. Source Core construction can depend on
the selected scheduler choice and may report a compiler/metadata error. Keep
that error at the chosen step with its current state; never synthesize a
fallback Core or eagerly reject configurations for choices that are not run. -/
def loopChecked (configs : C → Except StepError (Core Os R P H D O Aff B Host C ClockHost))
    (limits : ExecutionMachine.Limits)
    (main : MainMachine.Hooks (U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi MIR.TyId) (ArgAbi MIR.TyId) Aff P)
    (base : RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind (U Os R P H D O Aff B Host)) :
    RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback :=
  let bound := MainMachine.bindLoop main base scheduler
  {bound with
    coreStep := fun choice state =>
      match configs choice with
      | .ok config => ExecutionStateTransport.step config limits choice state
      | .error error => (state, .error error)
    invokeStackEmptyCallback := fun choice callback state =>
      match configs choice with
      | .error error => (state, .error error)
      | .ok config =>
        let h := mainCalls config limits main
        MachineHooks.run (match callback with
          | .main _ => MainMachine.invoke h choice
          | .tls callback => ThreadLoops.invoke h.termination.tls choice callback) state}

/-- Ready-state finite prefixes use the same fixed Config step and actual local
thread-stack scheduler while leaving stack-empty callback/termination behavior
as explicit source hooks. This is for a caller that has already initialized a
real frame and stops before requesting an unavailable callback. -/
def fixedCorePrefixLoop (configs : C → Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (base : RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind (U Os R P H D O Aff B Host)) :
    RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback :=
  let scheduled := ThreadStacks.bindRunLoop base scheduler
  {scheduled with coreStep := fun choice => ExecutionStateTransport.step (configs choice) limits choice}

/-- The specification ranges over every permitted finite execution prefix;
resource-bounded execution is not used as its safety definition. -/
def ubFreedom (configs : C → Core Os R P H D O Aff B Host C ClockHost) (limits : ExecutionMachine.Limits)
    (main : MainMachine.Hooks (U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi MIR.TyId) (ArgAbi MIR.TyId) Aff P)
    (base : RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind (U Os R P H D O Aff B Host))
    (allowed : EvalWorld.State Os R P H D O Aff B Host → C → Prop)
    (initial : EvalWorld.State Os R P H D O Aff B Host → Prop) : Prop :=
  RunLoop.UBFreedomFrom (loop configs limits main base scheduler) allowed initial

end Miri.Input.EvalExecutable
