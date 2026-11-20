import Miri.Interpreter.Step

/-! Control transitions from pinned `eval_context.rs:513–558`,
`call.rs:1134–1210`, and `step.rs:537–707`. Required callbacks carry the
remaining interpreter operations; this is not a closed Rust semantics. -/
namespace Miri.Interpreter
open Miri.MIR

structure ControlHooks (P L E M C Op : Type) where
  bodySpan : Frame P L E → Except StepError SpanRef
  returnOperand : C → StepState P L E M → StepResult (StepState P L E M) Op
  popFrame : C → StepState P L E M →
    StepResult (StepState P L E M) (Frame P L E)
  copyReturn : C → Op → RuntimeStackPlace P → StepState P L E M →
    StepResult (StepState P L E M) Unit
  cleanupFrame : C → Bool → Frame P L E → StepState P L E M →
    StepResult (StepState P L E M) ReturnAction
  unwindTerminate : C → UnwindTerminateReason → StepState P L E M →
    StepResult (StepState P L E M) Unit

namespace ControlFlow
variable {P L E M C Op : Type}
local notation "State" => StepState P L E M
local notation "Hooks" => ControlHooks P L E M C Op

/-- Source jumps assign the location directly; target validation belongs to
body loading/next step, not an extra check before this assignment. -/
def setLocation (state : State) (location : FrameLocation) : StepResult State Unit :=
  match state.stack.currentFrame? with
  | none => (state, .error (.stack .emptyStack))
  | some frame =>
    ({ state with stack := ⟨state.stack.frames.pop.push { frame with location }⟩ }, .ok ())

def goToBlock (target : BasicBlockId) (state : State) : StepResult State Unit :=
  setLocation state (.mir ⟨target, 0⟩)

def returnToBlock (target : Option BasicBlockId) (state : State) : StepResult State Unit :=
  match target with
  | some block => goToBlock block state
  | none => (state, .error (.undefinedBehavior "Unreachable"))

def unwindToBlock (hooks : Hooks) (choice : C) (target : UnwindAction)
    (state : State) : StepResult State Unit := Id.run do
  match target with
  | .Cleanup block => return goToBlock block state
  | .Unreachable =>
    return (state, .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))
  | .Continue | .Terminate _ =>
    let some frame := state.stack.currentFrame? |
      return (state, .error (.stack .emptyStack))
    let span ← match hooks.bodySpan frame with
      | .error error => return (state, .error error)
      | .ok span => pure span
    let (state, result) := setLocation state (.unwinding span)
    match result with
    | .error error => return (state, .error error)
    | .ok () =>
      match target with
      | .Terminate reason => return hooks.unwindTerminate choice reason state
      | _ => return (state, .ok ())

/-- Return reads local 0 even on unwind, pops before copying, then performs
cleanup before following the continuation. Every error preserves prior effects. -/
def returnFromCurrentFrame (hooks : Hooks) (choice : C) (unwinding : Bool)
    (state : State) : StepResult State Unit := Id.run do
  let some frame := state.stack.currentFrame? |
    return (state, .error (.stack .emptyStack))
  let isCleanup ← match frame.location with
    | .unwinding _ => pure true
    | .mir loc =>
      match frame.body.basicBlocks[loc.block]? with
      | none => return (state, .error (.invalidBlock loc.block))
      | some block => pure block.cleanup
  if unwinding != isCleanup then
    return (state, .error (.invalidProgram "return/unwind cleanup assertion failed"))
  if unwinding && state.stack.frames.size == 1 then
    return (state, .error (.undefinedBehavior "unwinding past the topmost stack frame"))
  let (state, value) := hooks.returnOperand choice state
  let value ← match value with
    | .error error => return (state, .error error)
    | .ok value => pure value
  let (state, popped) := hooks.popFrame choice state
  let frame ← match popped with
    | .error error => return (state, .error error)
    | .ok frame => pure frame
  let mut state := state
  if !unwinding then
    let (next, copied) := hooks.copyReturn choice value frame.returnPlace state
    state := next
    match copied with
    | .error error => return (state, .error error)
    | .ok () => pure ()
  let (cleanedState, cleaned) := hooks.cleanupFrame choice unwinding frame state
  state := cleanedState
  let action ← match cleaned with
    | .error error => return (state, .error error)
    | .ok action => pure action
  match action with
  | .noJump => return (state, .ok ())
  | .noCleanup =>
    if !state.stack.frames.isEmpty || unwinding then
      return (state, .error (.invalidProgram "NoCleanup requires empty stack and normal return"))
    return (state, .ok ())
  | .normal =>
    match frame.returnContinuation with
    | .goto ret unwind =>
      if unwinding then return unwindToBlock hooks choice unwind state
      return returnToBlock ret state
    | .stop _ =>
      if unwinding || !state.stack.frames.isEmpty then
        return (state, .error (.invalidProgram "Stop continuation requires normal root return"))
      return (state, .ok ())

end ControlFlow

structure TerminatorHooks (P L E M C Op Imm : Type) extends ControlHooks P L E M C Op where
  evalDiscriminant : C → MIR.Operand → StepState P L E M →
    StepResult (StepState P L E M) Imm
  /-- Must run MIR Eq against a same-layout `ImmTy::from_uint`, then to_bool;
  raw pointer discriminants must not be converted to integer addresses here. -/
  compareSwitchCase : C → Imm → Nat → StepState P L E M →
    StepResult (StepState P L E M) Bool
  call : C → Terminator → StepState P L E M → StepResult (StepState P L E M) Unit
  tailCall : C → Terminator → StepState P L E M → StepResult (StepState P L E M) Unit
  drop : C → Place → BasicBlockId → UnwindAction → StepState P L E M →
    StepResult (StepState P L E M) Unit
  ignoreOptionalOverflowChecks : StepState P L E M → Bool
  readAssertCondition : C → MIR.Operand → StepState P L E M →
    StepResult (StepState P L E M) Bool
  assertPanic : C → AssertKind → UnwindAction → StepState P L E M →
    StepResult (StepState P L E M) Unit

namespace ControlFlow
variable {P L E M C Op Imm : Type}
local notation "State" => StepState P L E M

/-- rustc's optional overflow checks are arithmetic overflow and negation. -/
def isOptionalOverflowCheck : AssertKind → Bool
  | .Overflow .Add .. | .Overflow .Sub .. | .Overflow .Mul ..
  | .Overflow .Shl .. | .Overflow .Shr .. | .OverflowNeg .. => true
  | _ => false

def evalTerminator (hooks : TerminatorHooks P L E M C Op Imm) (choice : C)
    (terminator : Terminator) (state : State) : StepResult State Unit := Id.run do
  match terminator.kind with
  | .Goto target _ => return goToBlock target state
  | .Return => return returnFromCurrentFrame hooks.toControlHooks choice false state
  | .UnwindResume => return returnFromCurrentFrame hooks.toControlHooks choice true state
  | .UnwindTerminate reason => return hooks.unwindTerminate choice reason state
  | .Unreachable => return (state, .error (.undefinedBehavior "Unreachable"))
  | .InlineAsm _ => return (state, .error (.unsupported "inline assembly"))
  | .FalseEdge .. | .FalseUnwind .. | .Yield .. | .CoroutineDrop =>
    return (state, .error (.invalidProgram "terminator should have been eliminated by MIR pass"))
  | .SwitchInt discr targets =>
    let (state, value) := hooks.evalDiscriminant choice discr state
    let value ← match value with
      | .error error => return (state, .error error)
      | .ok value => pure value
    let mut state := state
    let mut target := targets.otherwise
    for case in targets.cases do
      let .Case bits block := case
      let (next, comparison) := hooks.compareSwitchCase choice value bits state
      state := next
      match comparison with
      | .error error => return (state, .error error)
      | .ok true => target := block; break
      | .ok false => pure ()
    return goToBlock target state
  | .Call _ _ _ target .. =>
    let oldIndex := state.stack.frames.size
    let oldLoc := state.stack.currentFrame?.map (·.location)
    let (state, result) := hooks.call choice terminator state
    match result with
    | .error error => return (state, .error error)
    | .ok () =>
      if target.isSome && state.stack.frames.size == oldIndex &&
          state.stack.currentFrame?.map (·.location) == oldLoc then
        return (state, .error (.invalidProgram "evaluating this call made no progress"))
      return (state, .ok ())
  | .TailCall .. =>
    let oldIndex := state.stack.frames.size
    let (state, result) := hooks.tailCall choice terminator state
    match result with
    | .error error => return (state, .error error)
    | .ok () =>
      if state.stack.frames.size != oldIndex then
        return (state, .error (.invalidProgram "tail call changed frame index"))
      return (state, .ok ())
  | .Drop place target unwind _ asyncDrop =>
    if asyncDrop.isSome then
      return (state, .error (.invalidProgram "Async Drop must be expanded or reset to sync"))
    return hooks.drop choice place target unwind state
  | .Assert condition expected message target unwind =>
    let ignored := hooks.ignoreOptionalOverflowChecks state && isOptionalOverflowCheck message
    let (state, value) := hooks.readAssertCondition choice condition state
    match value with
    | .error error => return (state, .error error)
    | .ok value =>
      if ignored || expected == value then return goToBlock target state
      return hooks.assertPanic choice message unwind state

end ControlFlow
end Miri.Interpreter
