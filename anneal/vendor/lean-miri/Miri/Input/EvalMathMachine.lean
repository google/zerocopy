import Miri.Input.CompilerProviders
import Miri.Input.EvalCoreMachine
import Miri.Interpreter.ExecutionMath

/-! Math construction on the canonical World. Host numerical operations and
source C-signature checking remain genuine capabilities; every choice draw
uses the single execution tape and every operand/store uses the MIR engine. -/
namespace Miri.Input.EvalMathMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
structure Host (S C : Type) where
  unary : C → Math.Unary → Math.HostBits → RvalueM S Math.HostBits
  binary : C → Math.Binary → Math.HostBits → Math.HostBits → RvalueM S Math.HostBits
  powi : C → Math.HostBits → Int32 → RvalueM S Math.HostBits
  lgamma : C → Math.HostBits → RvalueM S (Math.HostBits × Int32)

/-- Absence of actual numerical host operations is an explicit capability
boundary at the call event, never a fabricated floating-point result. -/
def optionalHost (host : Option (Host S C)) : Host S C where
  unary := fun choice operation value => match host with
    | some host => host.unary choice operation value
    | none => throw (.unsupported "host unary math requires actual numerical capability")
  binary := fun choice operation left right => match host with
    | some host => host.binary choice operation left right
    | none => throw (.unsupported "host binary math requires actual numerical capability")
  powi := fun choice value exponent => match host with
    | some host => host.powi choice value exponent
    | none => throw (.unsupported "host powi requires actual numerical capability")
  lgamma := fun choice value => match host with
    | some host => host.lgamma choice value
    | none => throw (.unsupported "host lgamma requires actual numerical capability")

/-- Source random calls consume a new tape entry at the callback event, not
one reused operation-wide index. Session error mode is an explicit real input. -/
def leaves (tape : ExecutionChoices.Access S) (host : Host S C) (mode : Math.ErrorMode)
    (signature : C → String → Nat → RvalueM S Unit) : ExecutionMath.Leaves S C where
  checkCSignature := signature
  hostUnary := host.unary
  hostBinary := host.binary
  hostPowi := host.powi
  hostLgamma := host.lgamma
  errorMode := mode
  ulpError := fun _ bound => ExecutionChoices.integer tape .floatUlp (-Int.ofNat bound) (Int.ofNat bound)
  maxErrorPositive := fun _ => ExecutionChoices.boolean tape .floatSign
  relativeMagnitude := fun _ precision => ExecutionChoices.index tape .floatMagnitude (2^precision)
  relativeNegative := fun _ => ExecutionChoices.boolean tape .floatSign
  snanPowNaN := fun _ => ExecutionChoices.boolean tape .signalingPow

/-- The i32 pointee identity comes from the compiler's exact primitive catalog.
No guessed type ID, overwritten MathHooks baseline, or empty choice defaults. -/
def hooks (p : CompilerProviders.Prepared)
    (host : Host (EvalCoreMachine.State Os R P H D O Aff B WorldHost) C) (mode : Math.ErrorMode)
    (signature : Option (C → String → Nat → RvalueM (EvalCoreMachine.State Os R P H D O Aff B WorldHost) Unit))
    (access : ValidityMachine.Access MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B WorldHost))
    (place : PlaceHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B WorldHost) C MachineHooks.FrameExtra)
    (scalar : ScalarOpsHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B WorldHost) C)
    (floats : FloatOpsHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B WorldHost) C)
    (returnToBlock : C → Option BasicBlockId → RvalueM (EvalCoreMachine.State Os R P H D O Aff B WorldHost) Unit) :
    Except StepError (Math.Hooks Provenance (EvalCoreMachine.State Os R P H D O Aff B WorldHost) C (RuntimePlace Provenance)) := do
  let i32 ← p.primitiveLayout "i32" |>.mapError
    (fun reason => .callback s!"compiler math i32 layout unavailable: {reason}")
  let checkSignature := fun choice name count => match signature with
    | some signature => signature choice name count
    | none => throw (.unsupported "C math shim requires actual caller ABI context")
  pure (ExecutionMath.hooks (leaves EvalCoreMachine.tape host mode checkSignature)
    access place scalar floats i32 returnToBlock)
end Miri.Input.EvalMathMachine
