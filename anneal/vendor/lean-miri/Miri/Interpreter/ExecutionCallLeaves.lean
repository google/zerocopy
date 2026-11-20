import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.VirtualCalls
import Miri.Interpreter.FunctionCalls
import Miri.Interpreter.CallDispatchMachine
import Miri.Interpreter.IntrinsicArchitecture

/-! Surviving compiler/platform capabilities of the source call constructor.
Frame/local operations, ABI projections, argument projection, retagging,
varargs storage and MIR/foreign/backend dispatch algorithms are not callbacks. -/
namespace Miri.Interpreter.ExecutionCallLeaves
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure TargetFeature where
  name : String
  implied : Bool
structure TargetFeatures (S : Type) where
  required : CallInstance → M S (Array TargetFeature)
  available : String → M S Bool
  isLikeWasm : M S Bool

/-- machine.rs check_fn_target_features: the first guard includes implied
features, while the reported list excludes them. WASM aborts instead of UB. -/
def checkTargetFeatures (h : TargetFeatures S) (callee : CallInstance) : M S Unit := do
  let features ← h.required callee
  let mut missing := false
  for feature in features do
    if !(← h.available feature.name) then
      missing := true
      break
  unless missing do return
  let mut unavailable := #[]
  for feature in features do
    if !feature.implied then
      unless ← h.available feature.name do unavailable := unavailable.push feature.name
  let message := "calling a function that requires unavailable target features: " ++
    String.intercalate ", " unavailable.toList
  if ← h.isLikeWasm then throw (.termination (.abort message))
  throw (.undefinedBehavior message)

structure Compiler (S C Extern : Type) where
  functionSignature : C → LocalLayout → M S (Nat × Extern)
  functionKind : TyId → M S CallFunctionKind
  resolve : C → DefId → Array GenericArg → M S CallInstance
  fnAbiOfFnPtr : C → LocalLayout → Array TyId → M S (FnAbi TyId)
  fnAbiOfInstance : C → CallInstance → Array TyId → M S (FnAbi TyId)
  isRustCall : Extern → Bool
  rustAbi : Extern
  checkArgumentCompat : C → ArgAbi TyId → ArgAbi TyId → M S Bool
  targetFeatures : TargetFeatures S
  tupleFields : TyId → M S (Array TyId)
  isClosureLike : CallInstance → M S Bool
  closureUpvarCount : TyId → M S (Option Nat)
  llvmLinkName : CallInstance → M S String
structure Hooks (S C Other Extern : Type) where
  compiler : Compiler S C Extern
  dispatch : CallDispatchMachine.Hooks S C Other
  llvm : CallInstance → EStateM StepError S (IntrinsicArchitecture.DispatchHooks Provenance S C (RuntimePlace Provenance))

/-- Source call.rs non-capturing-closure test, including its short circuit.
ClosureOnce avoids the def-kind query; the first ABI argument is touched only
for closure-like instances, and upvars only for a Closure type. -/
def nonCapturingClosure (h : Compiler S C X) (callee : CallInstance) (abi : FnAbi TyId) : M S Bool := do
  let closureLike ← match callee.kind with
    | .Shim (.ClosureOnce ..) => pure true
    | _ => h.isClosureLike callee
  unless closureLike do return false
  let some first := abi.args[0]? | throw (.invalidProgram "closure-like function has no self ABI")
  match ← h.closureUpvarCount first.layout.ty with
  | some count => pure (count == 0)
  | none => pure false
/-- Virtual compiler/vtable data and actual alignment-state access only. -/
structure Virtual (K U C : Type) where
  compiler : VirtualCalls.CompilerHooks (MachineHooks.State K U) C
  vtable : VTableHooks Provenance (MachineHooks.State K U) C CallInstance (FnAbi TyId)
  alignment : PointerPlaceMachine.AlignmentContext U

/-- The actual shared locals-buffer ghost-identity supply. Callers provide a
representation lens, not a callback that chooses a frame identity. -/
structure IdentityAccess (U : Type) where
  get : U → LocalsIdentitySupply
  put : U → LocalsIdentitySupply → U

/-- Source helper signature queries/data only; actual call/stack/origin actions
are constructed from the canonical machine state. -/
structure Helpers (S C Extern : Type) where
  loadMir : C → CallInstance → M S LoadedBody
  unitLayout : LocalLayout
  fnAbiOfSignature : C → FunctionCalls.SignatureRequest Extern → M S (FnAbi TyId)
  callerLocationType : M S TyId
  dummySpan : SpanRef
end Miri.Interpreter.ExecutionCallLeaves
