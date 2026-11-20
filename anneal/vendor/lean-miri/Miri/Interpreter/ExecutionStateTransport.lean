import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.AtomicMachine
import Miri.Interpreter.ThreadStacks

/-! Canonical state reassociation. Source machine validation/alignment/ghost
fields and the alloc-address symbolic-alignment map each have exactly one
owner. This changes record nesting only: no frame, memory, clock or cache is
created. Error results are transported with their actual partially updated state.
-/
namespace Miri.Interpreter.ExecutionStateTransport
open Miri.Memory
abbrev Outer U := ThreadStacks.Storage (ValidityMachine.UserState U)
abbrev Inner U := ValidityMachine.UserState (ThreadStacks.Storage U)

def toInner (u : Outer U) : Inner U :=
  {u.user with payload := {u.user.payload with payload :=
    ⟨u.registry,u.identitySupply,u.user.payload.payload⟩}}
def toOuter (u : Inner U) : Outer U :=
  ⟨u.payload.payload.registry,u.payload.payload.identitySupply,
    {u with payload := {u.payload with payload := u.payload.payload.user}}⟩
@[simp] theorem outer_roundtrip (u : Outer U) : toOuter (toInner u) = u := rfl
@[simp] theorem inner_roundtrip (u : Inner U) : toInner (toOuter u) = u := rfl

def inward (s : MachineHooks.State K (Outer U)) : MachineHooks.State K (Inner U) :=
  ⟨s.stack,{s.machine with user := toInner s.machine.user}⟩
def outward (s : MachineHooks.State K (Inner U)) : MachineHooks.State K (Outer U) :=
  ⟨s.stack,{s.machine with user := toOuter s.machine.user}⟩
@[simp] theorem outward_inward (s : MachineHooks.State K (Outer U)) : outward (inward s) = s := rfl
@[simp] theorem inward_outward (s : MachineHooks.State K (Inner U)) : inward (outward s) = s := rfl

/-- Run an existing validity/pointer/atomic operation on the same actual state. -/
def action (a : MachineHooks.M K (Inner U) A) : MachineHooks.M K (Outer U) A := fun s =>
  match a (inward s) with
  | .ok v after => .ok v (outward after)
  | .error e after => .error e (outward after)
/-- Outer scheduler/registry/compiler operations can be used by inner drivers. -/
def reverseAction (a : MachineHooks.M K (Outer U) A) : MachineHooks.M K (Inner U) A := fun s =>
  match a (outward s) with
  | .ok v after => .ok v (inward after)
  | .error e after => .error e (inward after)

def scalar (h : ScalarOpsHooks P (MachineHooks.State K (Inner U)) C) :
    ScalarOpsHooks P (MachineHooks.State K (Outer U)) C where
  classify := fun c t => action (h.classify c t)
  boolLayout := fun c => action (h.boolLayout c)
  orderingLayout := fun c => action (h.orderingLayout c)
  overflowLayout := fun c l => action (h.overflowLayout c l)
  metadataLayout := fun c t => action (h.metadataLayout c t)
  unitLayout := fun c => action (h.unitLayout c)
  floatBinary := fun c op l r => action (h.floatBinary c op l r)
  pointerBinary := fun c op l r => action (h.pointerBinary c op l r)
  floatUnary := fun c op v => action (h.floatUnary c op v)
  derefValidity := fun c v => action (h.derefValidity c v)

def atomic (h : IntrinsicAtomicHooks P (MachineHooks.State K (Inner U)) C V) :
    IntrinsicAtomicHooks P (MachineHooks.State K (Outer U)) C V where
  target := h.target
  getGlobal := fun s => h.getGlobal (inward s)
  setGlobal := fun s g => outward (h.setGlobal (inward s) g)
  threads := fun s => h.threads (inward s)
  getAtomic := fun s id => h.getAtomic (inward s) id
  setAtomic := fun id a => action (h.setAtomic id a)

  orderingConst := fun c n => action (h.orderingConst c n)
  volatileConst := fun c n => action (h.volatileConst c n)
  derefPointer := fun c v => action (h.derefPointer c v)
  placeLayout := h.placeLayout
  placePointer := h.placePointer
  readImmediate := fun c v => action (h.readImmediate c v)
  physicalRead := fun c v => action (h.physicalRead c v)
  physicalWrite := fun c v p => action (h.physicalWrite c v p)
  ghostRead := fun c v => action (h.ghostRead c v)
  checkPointerAlign := fun c p a => action (h.checkPointerAlign c p a)
  resolveAllocation := fun c p => action (h.resolveAllocation c p)
  mutability := fun c id => action (h.mutability c id)
  scalarOps := scalar h.scalarOps
  writeImmediate := fun c v p => action (h.writeImmediate c v p)
  returnToBlock := fun c b => action (h.returnToBlock c b)
  loadChoiceRank := fun c n => action (h.loadChoiceRank c n)
  weakPolicy := h.weakPolicy
  weakSuccessChoice := fun c => action (h.weakSuccessChoice c)
  diagnostic := fun c d => action (h.diagnostic c d)
  classifyDispatchError := h.classifyDispatchError
  classifyGlobalError := h.classifyGlobalError

/-- Assemble the actual canonical physical atomic pipeline, then transport its
complete dictionary. This is not a second atomic implementation. -/
def atomicMachine [DecidableEq K]
    (base : IntrinsicAtomicHooks Provenance (MachineHooks.State K (Inner U)) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig K (Inner U))
    (allocation : PlaceMachine.AllocationConfig K (Inner U))
    (compiler : PlaceMachine.CompilerHooks K (Inner U) C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control (ThreadStacks.Storage U)))
    (extras : MemoryExtras.Hooks K (Inner U) Payload) :=
  atomic (AtomicMachine.bind base access allocation compiler pointers extras)

/-- The pointer dictionary's source effects run against the canonical address,
provenance and symbolic-alignment state carried by the reassociation. -/
def pointerAllocation (h : PointerMachine.Hooks K (ValidityMachine.Control (ThreadStacks.Storage U)))
    (p : Pointer Provenance) (size : Int64) := action (PointerMachine.ptrGetAlloc h p size)

def exposeProvenance [DecidableEq K]
    (h : PointerMachine.Hooks K (ValidityMachine.Control (ThreadStacks.Storage U)))
    (p : Provenance) := action (PointerMachine.exposeProvenance h p)

/-- The scope encloses the entire transported action. Restoration uses the
post-action Control, retaining failures, registry updates and cached unions. -/
def withGhostValidation (a : MachineHooks.M K (Outer U) A) : MachineHooks.M K (Outer U) A :=
  action (ValidityMachine.withGhostValidation (reverseAction a))

def enforceValidity : MachineHooks.M K (Outer U) Bool :=
  action ValidityMachine.enforceValidity

def enforceValidityRecursively : MachineHooks.M K (Outer U) Bool :=
  action ValidityMachine.enforceValidityRecursively

def readImmediate [DecidableEq K] (access : PlaceMachine.AccessConfig K (Inner U))
    (value : OpTy Provenance) := action (ValidityMachine.readImmediate access value)

/-- Whole MIR execution uses the existing full source assembly with all its
physical/validation dictionaries instantiated at Inner U. Outer state keeps
its scheduler-facing ThreadStacks representation between steps. -/
def step [DecidableEq K] (h : ExecutionMachine.Config K (Inner U) C O X Host)
    (limits : ExecutionMachine.Limits) (c : C) (s : MachineHooks.State K (Outer U)) :
    StepResult (MachineHooks.State K (Outer U)) Bool :=
  let (after,result) := ExecutionMachine.step h limits c (inward s)
  (outward after,result)
end Miri.Interpreter.ExecutionStateTransport
