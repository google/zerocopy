import Miri.Input.CompilerVirtualLeaves
import Miri.Input.CompilerProviders
import Miri.Input.CompilerCallFacts
import Miri.Input.CompilerExecutionCallLeaves
import Miri.Interpreter.ExecutionCalls

/-! Actual compiler call construction; no complete operational CallHooks record
is accepted and discarded. Every query key uses the canonical compilation. -/
namespace Miri.Input.CompilerCallConstruction
open Lean Miri.ABI Miri.Memory Miri.Interpreter
private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

/-- Canonical full compiler dictionary, including target-feature policy. -/
def compiler (p : CompilerProviders.Prepared) (budget : Nat) :
    ExecutionCallLeaves.Compiler (MachineHooks.State K U) C ABI.ExternAbi :=
  CompilerExecutionCallLeaves.make p budget

/-- Foreign emulation and real backend hooks are actual source interpreters;
MIR loading is the same exact LoadedBody provider used by helper/root calls. -/
def dispatch (p : CompilerProviders.Prepared)
    (foreign : Option (MachineHooks.M K U (ForeignItems.Hooks Provenance
      (MachineHooks.State K U) (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)))
    (backend : CallDispatchMachine.Backend (MachineHooks.State K U)) (dynSymName : Other → String) :
    CallDispatchMachine.Hooks (MachineHooks.State K U) C Other where
  foreign := foreign
  returnToBlock := fun target state =>
    let (after,result) := ControlFlow.returnToBlock target state
    match result with | .ok value => .ok value after | .error error => .error error after
  backend := backend
  dynSymName := dynSymName
  foreignScope := fun action => action
  isForeignItem := fun callee => lift (CompilerCallFacts.isForeignItem p.intrinsics callee)
  symbolName := fun callee => lift (CompilerCallFacts.symbolName p.intrinsics callee)
  loadMir := fun _ callee => CompilerCallPipeline.loadMir p.lifecycle.calls callee

def leaves (p : CompilerProviders.Prepared) (compatibilityBudget : Nat)
    (foreign : Option (MachineHooks.M K U (ForeignItems.Hooks Provenance
      (MachineHooks.State K U) (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)))
    (backend : CallDispatchMachine.Backend (MachineHooks.State K U)) (dynSymName : Other → String)
    (llvm : CallInstance → MachineHooks.M K U (IntrinsicArchitecture.DispatchHooks Provenance (MachineHooks.State K U) C (RuntimePlace Provenance))) :
    ExecutionCallLeaves.Hooks (MachineHooks.State K U) C Other ABI.ExternAbi :=
  ⟨compiler p compatibilityBudget,dispatch p foreign backend dynSymName,llvm⟩
/-- Shared canonical vtable queries plus the exact compiler virtual leaves;
receiver reads, projections and pointer construction are not caller callbacks. -/
def virtual (p : CompilerProviders.Prepared)
    (vtable : VTableHooks Provenance (MachineHooks.State K U) C CallInstance (FnAbi MIR.TyId))
    (alignment : PointerPlaceMachine.AlignmentContext U) : ExecutionCallLeaves.Virtual K U C :=
  ⟨CompilerVirtualLeaves.make p.lifecycle.calls,vtable,alignment⟩

/-- Source frame metadata, preamble/checks and after-pop unwind processing.
Storage is the actual shared machine allocation context; no raw-push or
post-initialization success callback is accepted. -/
def lifecycle (p : CompilerProviders.Prepared) (userRelevantCrates : Array Nat)
    (storage : MachineHooks.StorageHooks K U) (identity : ExecutionCallLeaves.IdentityAccess U)
    (unwind : Unwind.Hooks K U C Other) : CallMachine.Lifecycle K U C where
  compiler := CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates
  storage := storage
  freshLocalsIdentity := fun machine =>
    let (supply,label) := (identity.get machine.user).allocate
    ({machine with user := identity.put machine.user supply},label)
  preambleSpan := CompilerLifecycle.preambleSpan p.lifecycle.lifecycle
  requiredConstants := CompilerLifecycle.requiredConstants p.lifecycle.lifecycle
  afterPop := fun choice frame unwinding => Unwind.afterStackPop unwind choice frame.extra unwinding

/-- Exact existing shared ThreadStacks supply, without a second counter. -/
def threadIdentity : ExecutionCallLeaves.IdentityAccess (ThreadStacks.Storage U) :=
  ⟨(·.identitySupply),fun user supply => {user with identitySupply := supply}⟩

/-- Actual source helper metadata plus the genuine dummy-signature compiler
query. Stack/origin operations are built by ExecutionCalls.helpers. -/
def helpers (p : CompilerProviders.Prepared) (dummySpan : MIR.SpanRef)
    (fnAbiOfSignature : C → FunctionCalls.SignatureRequest ABI.ExternAbi → MachineHooks.M K U (FnAbi MIR.TyId)) :
    Except String (ExecutionCallLeaves.Helpers (MachineHooks.State K U) C ABI.ExternAbi) := do
  let unit ← p.primitiveLayout "unit"
  return {
    loadMir := fun _ callee => CompilerCallPipeline.loadMir p.lifecycle.calls callee
    unitLayout := unit
    fnAbiOfSignature := fnAbiOfSignature
    callerLocationType := lift p.callerLocationType
    dummySpan }
end Miri.Input.CompilerCallConstruction
