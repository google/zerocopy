import Miri.Interpreter.Unwind

/-! Pinned helpers.rs::call_function and call_thread_root_function. This driver
uses the canonical Call.initStackFrame rather than treating a successful call
as an opaque foreign effect. The compiler's construction of a dummy-binder
function-pointer signature and its ABI query remain explicit query operations.
-/
namespace Miri.Interpreter.FunctionCalls
open Miri.ABI Miri.Memory Miri.MIR

/-- `mk_fn_sig` receives these exact input/output types, Safe safety, the given
ABI, and the source defaults (not C variadic or splatted). This is a compiler
query request, not another executable program representation. -/
structure SignatureRequest (Extern : Type) where
  inputs : Array TyId
  output : TyId
  abi : Extern
  safety : Safety
  cVariadic : Bool
  splatted : Bool

structure Hooks (P S C E Other Extern FnABI ArgABI : Type) where
  call : CallHooks P S C E Other Extern FnABI ArgABI
  /-- load_mir(f.def, None), before constructing destination/signature. -/
  loadMir : C → CallInstance → CallM S LoadedBody
  unitLayout : LocalLayout
  /-- Actual mk_fn_sig + Binder::dummy + fn_abi_of_fn_ptr(..., empty).
  No existential type/ABI chosen by the proof user is permitted here. -/
  fnAbiOfSignature : C → SignatureRequest Extern → CallM S FnABI
  callerLocationType : CallM S TyId
  activeStackEmpty : CallM S Bool
  /-- Compare the actual active thread's origin Span to DUMMY_SP. -/
  originIsDummy : CallM S Bool
  setOrigin : SpanRef → CallM S Unit

/-- Source place.rs::fake_alloc_zst. No allocation, borrow/race event, or fresh
provenance is introduced. Its absolute address is the ABI alignment in bytes. -/
def fakeAllocZst (layout : LocalLayout) : Except StepError (MPlaceTy P) := do
  if !layout.layout.isSized || layout.layout.size != .ZERO then
    throw (.invalidProgram "fake_alloc_zst called with a non-ZST layout")
  let address ← match layout.layout.align.abi.bytes with
    | .ok address => pure address
    | .error error => throw (.invalidProgram s!"fake_alloc_zst alignment: {reprStr error}")
  return ⟨⟨Pointer.withoutProvenance address, .none, none⟩, layout⟩

/-- Internal helper calls pass immediate copies; track_caller changes the
caller signature, not the explicit argument array. initStackFrame supplies the
caller-location argument according to the canonical source call pipeline. -/
def callFunction (h : Hooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (fnInstance : CallInstance) (callerAbi : Extern) (args : Array (RvalueImmTy P))
    (destination : Option (MPlaceTy P)) (continuation : ReturnContinuation) : CallM S Unit := do
  let body ← h.loadMir choice fnInstance
  let destination ← match destination with
    | some place => pure place
    | none => match fakeAllocZst h.unitLayout with
      | .ok place => pure place
      | .error error => throw error
  let withCallerLocation ← h.call.requiresCallerLocation fnInstance
  let mut inputs := args.map (fun arg => arg.layout.ty)
  if withCallerLocation then inputs := inputs.push (← h.callerLocationType)
  let callerFnAbi ← h.fnAbiOfSignature choice {
    inputs, output := destination.layout.ty, abi := callerAbi,
    safety := .Safe, cVariadic := false, splatted := false }
  let copies := args.map (fun arg => FnArg.Copy ⟨.immediate arg.imm,arg.layout⟩)
  Call.initStackFrame h.call choice fnInstance body callerFnAbi copies
    withCallerLocation (.memory destination) continuation

/-- Source assertions are interpreter representation errors, not Rust UB.
Origin is assigned before any load_mir/compiler query, and retained if it fails. -/
def callThreadRootFunction (h : Hooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (fnInstance : CallInstance) (callerAbi : Extern) (args : Array (RvalueImmTy P))
    (destination : Option (MPlaceTy P)) (span : SpanRef) : CallM S Unit := do
  unless ← h.activeStackEmpty do
    throw (.invalidProgram "call_thread_root_function: nonempty active stack")
  unless ← h.originIsDummy do
    throw (.invalidProgram "call_thread_root_function: origin is not DUMMY_SP")
  h.setOrigin span
  callFunction h choice fnInstance callerAbi args destination (.stop true)

/-- Install the internal Rust call helper in the panic/unwind driver while
retaining all actual memory/function-pointer and payload operations. -/
def bindUnwind (base : Unwind.Hooks K User C Other)
    (h : Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      Other Extern FnABI ArgABI) : Unwind.Hooks K User C Other :=
  { base with callFunction := fun choice fnInstance args continuation =>
      callFunction h choice fnInstance h.call.rustAbi args none continuation }

end Miri.Interpreter.FunctionCalls
