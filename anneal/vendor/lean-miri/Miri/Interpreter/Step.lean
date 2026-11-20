import Miri.Interpreter.Stack
import Miri.Concurrency.Termination

/-! Small-step driver port of pinned rustc `interpret/step.rs:41-154`.
Callbacks are mandatory semantic obligations, including their mutations on failure. -/
namespace Miri.Interpreter
open Miri.MIR

structure StepState (Prov Layout Extra Machine : Type) where
  stack : Stack Prov Layout Extra
  machine : Machine

inductive StepError where
  | termination (info : Miri.Concurrency.TerminationInfo)
  | stack (error : StackError)
  | invalidBlock (block : BasicBlockId)
  | frameIndexChanged (before after : Nat)
  | expectedMirLocation
  | undefinedBehavior (reason : String)
  /-- Typed retag failure used by validity.rs before its source diagnostic mapping. -/
  | retagWriteToReadOnly
  | unsupported (reason : String)
  | invalidProgram (reason : String)
  | resourceExhaustion (reason : String)
  | machineStop (reason : String)
  | callback (message : String)
  deriving Repr, DecidableEq

abbrev StepResult (S A : Type) := S × Except StepError A

/-- Required interpreter operations. Choice inputs are explicit; no operation
has a default successful implementation. `evalPlace` receives the source's
`skip_validity_for_simple_deref = false` argument. -/
structure StepHooks (Prov Layout Extra Machine Choice PlaceValue : Type) where
  assign : Choice → Place → Rvalue → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  evalPlace : Choice → Place → Bool → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) PlaceValue
  writeDiscriminant : Choice → VariantIndex → PlaceValue → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  storageLive : Choice → LocalId → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  storageDead : Choice → LocalId → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  intrinsic : Choice → NonDivergingIntrinsic → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  incrementConstEvalCounter : Choice → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  returnFromCurrentFrame : Choice → Bool → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  beforeTerminator : Choice → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit
  terminator : Choice → Terminator → StepState Prov Layout Extra Machine →
    StepResult (StepState Prov Layout Extra Machine) Unit

namespace Step
variable {P L E M C V : Type}
local notation "State" => StepState P L E M
local notation "Hooks" => StepHooks P L E M C V

def evalStatement (hooks : Hooks) (choice : C) (stmt : Statement)
    (state : State) : StepResult State Unit :=
  match stmt.kind with
  | .Assign place value => hooks.assign choice place value state
  | .SetDiscriminant place variant =>
    let (state, result) := hooks.evalPlace choice place false state
    match result with
    | .error error => (state, .error error)
    | .ok place => hooks.writeDiscriminant choice variant place state
  | .StorageLive localId => hooks.storageLive choice localId state
  | .StorageDead localId => hooks.storageDead choice localId state
  | .Intrinsic intrinsic => hooks.intrinsic choice intrinsic state
  | .PlaceMention place =>
    let (state, result) := hooks.evalPlace choice place false state
    (state, result.map fun _ => ())
  | .ConstEvalCounter => hooks.incrementConstEvalCounter choice state
  | .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop
  | .BackwardIncompatibleDropHint .. => (state, .ok ())

private def finish (result : StepResult State Unit) : StepResult State Bool :=
  (result.1, result.2.map fun _ => true)

/-- Execute exactly one source driver iteration. A callback failure retains
its resulting state and stops immediately, before any subsequent operation. -/
def step (hooks : Hooks) (choice : C) (state : State) : StepResult State Bool := Id.run do
  match state.stack.currentFrame? with
  | none => return (state, .ok false)
  | some frame =>
    match frame.location with
    | .unwinding _ => return finish (hooks.returnFromCurrentFrame choice true state)
    | .mir loc =>
      let some block := frame.body.basicBlocks[loc.block]? |
        return (state, .error (.invalidBlock loc.block))
      match block.statements[loc.statementIndex]? with
      | some stmt =>
        let oldIndex := state.stack.frames.size - 1
        let (state, result) := evalStatement hooks choice stmt state
        match result with
        | .error error => return (state, .error error)
        | .ok () =>
          let newIndex := state.stack.frames.size - 1
          if oldIndex != newIndex then
            return (state, .error (.frameIndexChanged oldIndex newIndex))
          let some current := state.stack.currentFrame? |
            return (state, .error (.stack .emptyStack))
          let .mir currentLoc := current.location |
            return (state, .error .expectedMirLocation)
          -- Advance the current location, not the saved location: callbacks may change it.
          let next := { currentLoc with statementIndex := currentLoc.statementIndex + 1 }
          -- Source increments without re-validating the location against its body.
          let index := state.stack.frames.size - 1
          if h : index < state.stack.frames.size then
            let stack := { state.stack with frames := state.stack.frames.set index (
              { current with location := .mir next }) h }
            return ({ state with stack }, .ok true)
          return (state, .error (.stack .emptyStack))
      | none =>
        let (state, result) := hooks.beforeTerminator choice state
        match result with
        | .error error => return (state, .error error)
        | .ok () => return finish (hooks.terminator choice block.terminator state)

/-- Relational semantics quantifies over permitted explicit choice inputs.
No enumeration or finite-support assumption is imposed on machine choices. -/
def AllowedStep (hooks : Hooks) (allowedChoice : State → C → Prop)
    (before after : State) (outcome : Except StepError Bool) : Prop :=
  ∃ choice, allowedChoice before choice ∧ step hooks choice before = (after, outcome)

end Step
end Miri.Interpreter
