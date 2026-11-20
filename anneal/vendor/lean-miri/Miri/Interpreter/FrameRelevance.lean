import Miri.Interpreter.MachineHooks
import Miri.Interpreter.Backtrace

namespace Miri.Interpreter.FrameRelevance
open Miri.MIR Miri.Memory Miri.Concurrency
open MachineHooks
private def lift (result : Except StepError A) : M K User A :=
  match result with | .ok value => pure value | .error error => throw error

/-- Reverse source search: topmost wins ties; 255 short-circuits. -/
def computeTop (stack : Stack P LocalLayout FrameExtra) (skip : Nat) : Option Nat := Id.run do
  let mut best : Option (Nat × UInt8) := none
  for index in (List.range stack.frames.size).reverse.drop skip do
    if let some frame := stack.frames[index]? then
      let relevance := frame.extra.userRelevance
      if relevance == 255 then return some index
      if best.isNone || best.any (fun entry => entry.2 < relevance) then
        best := some (index, relevance)
  return best.map Prod.fst

def top (stack : Stack P LocalLayout FrameExtra) (cached : Option Nat) : Option Nat :=
  cached.orElse fun _ => if stack.frames.isEmpty then none else some (stack.frames.size - 1)

private def active : M K User ThreadRecord := do
  let some thread := (← get).machine.threads.activeThread?
    | throw (.invalidProgram "active relevance thread missing")
  return thread

private def setCache (value : Option Nat) : M K User Unit := do
  let _ ← active
  modify fun state => { state with machine := { state.machine with threads := {
    state.machine.threads with threads := state.machine.threads.threads.mapIdx fun index thread =>
      if index == state.machine.threads.activeThread.toNat then
        { thread with topUserRelevantFrame := value } else thread } } }

def afterStackPush (debugAssertions : Bool) : M K User Unit := do
  let frame ← currentFrame
  let thread ← active
  let stack := (← get).stack
  let current ← match top stack thread.topUserRelevantFrame with
    | none => pure 0
    | some index =>
      match stack.frames[index]? with
      | none => throw (.invalidProgram "user relevance cache index out of bounds")
      | some frame => pure frame.extra.userRelevance
  if frame.extra.userRelevance >= current then
    let index := stack.frames.size - 1
    if debugAssertions && computeTop stack 0 != some index then
      throw (.invalidProgram "debug assertion: top user relevant frame")
    setCache (some index)

/-- Invoke after successful TB on_stack_pop, before removing the frame. -/
def beforeStackPop : M K User Unit := do
  let thread ← active
  let stack := (← get).stack
  let some index := top stack thread.topUserRelevantFrame
    | throw (.invalidProgram "stack pop missing user relevant frame")
  if index == stack.frames.size - 1 then setCache (computeTop stack 1)

def currentUserRelevantSpan (debugAssertions : Bool) (dummy : SpanRef) : M K User SpanRef := do
  let thread ← active
  let stack := (← get).stack
  if debugAssertions && thread.topUserRelevantFrame != computeTop stack 0 then
    throw (.invalidProgram "debug assertion: cached user relevant frame")
  match top stack thread.topUserRelevantFrame with
  | none => return dummy
  | some index =>
    let some frame := stack.frames[index]?
      | throw (.invalidProgram "user relevance span index out of bounds")
    lift (Backtrace.currentSpan frame)

def callerSpan : M K User SpanRef := do
  let thread ← active
  let stack := (← get).stack
  let some index := top stack thread.topUserRelevantFrame
    | throw (.invalidProgram "caller_span requires frame")
  let some frame := stack.frames[min index (stack.frames.size - 2)]?
    | throw (.invalidProgram "caller_span index out of bounds")
  lift (Backtrace.currentSpan frame)

/-- Install source after_stack_push and the cache suffix of before_stack_pop.
The supplied beforePop is the borrow-tracker prefix; its failure retains its
state and never executes the cache update. Other lifecycle operations are retained. -/
def bindLifecycle (debugAssertions : Bool)
    (base : StackLifecycleHooks Provenance LocalLayout FrameExtra (MachineState K User)) :
    StackLifecycleHooks Provenance LocalLayout FrameExtra (MachineState K User) :=
  let execute := fun (action : M K User Unit)
      (stack : Stack Provenance LocalLayout FrameExtra) (machine : MachineState K User) =>
    let (state, outcome) := MachineHooks.run action ⟨stack, machine⟩
    ({ stack := state.stack, state := state.machine,
       outcome := outcome.mapError fun error => StackError.machineHookFailure (reprStr error) } :
      StackRunResult Provenance LocalLayout FrameExtra (MachineState K User) Unit)
  { base with
    afterPush := execute (afterStackPush debugAssertions)
    beforePop := fun stack machine =>
      let before := base.beforePop stack machine
      match before.outcome with
      | .error _ => before
      | .ok () => execute beforeStackPop before.stack before.state }

end Miri.Interpreter.FrameRelevance

namespace Miri.Interpreter.FrameRelevance
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
set_option autoImplicit false
variable {K U : Type}
abbrev FreshFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra
 def pushedMachine (frames : Array FreshFrame) (frame old : FreshFrame)
    (machine : MachineHooks.MachineState K U) :=
  if frame.extra.userRelevance >= old.extra.userRelevance then
    {machine with threads := {machine.threads with threads := machine.threads.threads.mapIdx fun index thread =>
      if index == machine.threads.activeThread.toNat then
        {thread with topUserRelevantFrame := some frames.size} else thread}}
  else machine
 theorem afterPush_known (frames : Array FreshFrame) (frame old : FreshFrame)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord) (index : Nat)
    (current : machine.threads.activeThread? = some thread)
    (cached : top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some index)
    (selected : (frames.push frame)[index]? = some old) :
    afterStackPush false (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok () ⟨⟨frames.push frame⟩,pushedMachine frames frame old machine⟩ := by
  simp [afterStackPush,MachineHooks.currentFrame,Stack.currentFrame?,active,setCache,
    current,cached,selected,pushedMachine,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  split <;> simp_all [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
end Miri.Interpreter.FrameRelevance
