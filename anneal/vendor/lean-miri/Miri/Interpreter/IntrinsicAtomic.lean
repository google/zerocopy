import Miri.Interpreter.ScalarOps
import Miri.Concurrency.AtomicAccess
import Miri.Concurrency.AtomicScalarMemory

/-! Core atomic intrinsic dispatch plus the Miri VClock/weak-memory pipeline.
Physical reads/writes must invoke the full interpreter memory/TB/sync hooks;
the restricted Unit-extra AtomicScalarMemory component is not promoted to a
complete atomic execution. Every finite permitted choice remains explicit. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency

inductive IntrinsicAtomicRmw where
  | mir (op : BinOp) (negate : Bool)
  | min | max | swap
  deriving DecidableEq, Repr
inductive WeakCasPolicy where
  | neverFail | alwaysFail | mayFail
  deriving DecidableEq, Repr
structure AtomicLocation where
  allocation : AllocId
  range : AllocRange
  deriving DecidableEq, Repr

structure AtomicAccessHooks (P S C V : Type) where
  target : TargetDataLayout
  getGlobal : S → Option GlobalState
  setGlobal : S → GlobalState → S
  threads : S → ThreadManager
  getAtomic : S → AllocId → Except StepError (AtomicState (Memory.Scalar P))
  setAtomic : AllocId → AtomicState (Memory.Scalar P) → RvalueM S Unit
  placeLayout : V → TyAndLayout TyId
  placePointer : V → Except StepError (Pointer (Option P))
  physicalRead : C → V → RvalueM S (RvalueImmTy P)
  physicalWrite : C → Immediate P → V → RvalueM S Unit
  ghostRead : C → V → RvalueM S (Option (Memory.Scalar P))
  checkPointerAlign : C → Pointer (Option P) → Align → RvalueM S Unit
  resolveAllocation : C → Pointer (Option P) → RvalueM S (AllocId × Size)
  mutability : C → AllocId → RvalueM S Memory.Mutability
  scalarOps : ScalarOpsHooks P S C
  loadChoiceRank : C → Nat → RvalueM S Nat
  weakPolicy : WeakCasPolicy
  weakSuccessChoice : C → RvalueM S Bool
  diagnostic : C → WeakMemoryDiagnostic → RvalueM S Unit
  classifyDispatchError : AtomicDispatchError → StepError
  classifyGlobalError : GlobalStateError → StepError

structure IntrinsicAtomicHooks (P S C V : Type) extends AtomicAccessHooks P S C V where
  orderingConst : C → Nat → RvalueM S Concurrency.AtomicOrdering
  volatileConst : C → Nat → RvalueM S Unit
  derefPointer : C → OpTy P → RvalueM S V
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  writeImmediate : C → Immediate P → V → RvalueM S Unit
  returnToBlock : C → Option BasicBlockId → RvalueM S Unit

instance : Coe (IntrinsicAtomicHooks P S C V) (AtomicAccessHooks P S C V) :=
  ⟨IntrinsicAtomicHooks.toAtomicAccessHooks⟩

namespace IntrinsicAtomic
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok value => pure value | .error error => throw error
private def scalar (value : RvalueImmTy P) : RvalueM S (Memory.Scalar P) :=
  liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
private def arity (args : Array (OpTy P)) (count : Nat) : RvalueM S Unit :=
  if args.size == count then pure () else invalid "atomic intrinsic argument count mismatch"
private def arg (args : Array (OpTy P)) (index : Nat) : RvalueM S (OpTy P) :=
  match args[index]? with | some value => pure value | none => invalid "atomic intrinsic missing argument"
private def convertOrdering (result : Except AtomicOrderingError A) : RvalueM S A :=
  match result with | .ok value => pure value | .error error => invalid s!"{repr error}"

/-- Exact source flag window, including restoration after physical-hook error.
Global lenses must view the same global state used by the memory access hooks. -/
def allowDataRaces (h : AtomicAccessHooks P S C V) (action : RvalueM S A) : RvalueM S A := fun state =>
  match h.getGlobal state with
  | none => action state
  | some global =>
    if global.ongoingActionDataRaceFree then
      .error (.invalidProgram "cannot nest allow_data_races") state
    else
      let active := h.setGlobal state (GlobalState.withDataRaceFreeAction global true)
      let restore := fun (state : S) => match h.getGlobal state with
        | none => Except.error (StepError.invalidProgram "atomic action removed vector-clock handler")
        | some global =>
          if !global.ongoingActionDataRaceFree then
            Except.error (StepError.invalidProgram "atomic data-race-free action flag was cleared")
          else Except.ok (h.setGlobal state (GlobalState.withDataRaceFreeAction global false))
      match action active with
      | .ok result state => match restore state with
        | .ok state => .ok result state
        | .error error => .error error state
      | .error error state => match restore state with
        | .ok state => .error error state
        | .error restoreError => .error restoreError state

private def raceDetecting (h : AtomicAccessHooks P S C V) (state : S) : Bool :=
  (h.getGlobal state).any GlobalState.raceDetecting

/-- Source atomic_access_check staging: size-derived alignment, pointer
alignment, allocation identity and read-only rules. Actual byte hooks follow. -/
def access (h : AtomicAccessHooks P S C V) (choice : C) (place : V)
    (kind : AtomicAccessKind) : RvalueM S AtomicLocation := do
  let size := (h.placeLayout place).layout.size
  let align ← match Align.fromBytes size.bytes with
    | .ok value => pure value | .error error => invalid s!"atomic alignment: {repr error}"
  let ptr ← liftResult (h.placePointer place)
  h.checkPointerAlign choice ptr align
  let (id, offset) ← h.resolveAllocation choice ptr
  let mutability ← h.mutability choice id
  let checked := atomicAccessCheck size (Size.fromBits h.target.pointerWidth.bits) kind
    ({ checkPtrAlign := fun _ => Except.ok ()
       pointerTryGetAllocId := Except.ok id
       getAllocMutability := fun _ => Except.ok mutability } : AtomicAccessOps AllocId Unit Unit)
  match checked with
  | .ok _ => pure ()
  | .error (.undefinedBehavior violation) => throw (.undefinedBehavior s!"readonly atomic access: {repr violation}")
  | .error _ => invalid "unexpected atomic access invariant failure"
  pure ⟨id, ⟨offset, size⟩⟩

/-- Commit post-byte/per-clock mutations even when a later byte or clock fails.
The state lens must preserve unrelated memory, provenance and borrow metadata. -/
def dispatch (h : AtomicAccessHooks P S C V) (location : AtomicLocation)
    (operation : AtomicState (Memory.Scalar P) → ThreadManager → AtomicTransition (Memory.Scalar P) A) : RvalueM S A := do
  let state ← get
  let atomic ← liftResult (h.getAtomic state location.allocation)
  let some global := h.getGlobal state | invalid "atomic dispatch requires vector clocks"
  let atomic := { atomic with global }
  let result := operation atomic (h.threads state)
  h.setAtomic location.allocation result.state
  modify fun state => h.setGlobal state result.state.global
  match result.outcome with
  | .ok result => pure result
  | .error error => throw (h.classifyDispatchError error)

def load (h : AtomicAccessHooks P S C V) (choice : C) (place : V)
    (ordering : Concurrency.AtomicOrdering) : RvalueM S (Memory.Scalar P) := do
  let ordering ← convertOrdering (AtomicReadOrd.ofOrdering ordering)
  let location ← access h choice place (.load ordering)

  let latest ← allowDataRaces h (h.physicalRead choice place)
  let latest ← scalar latest
  if !raceDetecting h (← get) then return latest
  let prepared ← dispatch h location fun state threads =>
    prepareBufferedAtomicRead state threads location.range ordering latest
  let result ← match prepared with
    | .ready result => pure result
    | .select handle clocks => do
      let count := (StoreBuffer.fetchChoices handle.buffer (ordering == .SeqCst) clocks).length
      let rank ← h.loadChoiceRank choice count
      dispatch h location fun state threads =>
        finishBufferedAtomicRead state threads location.range ordering handle clocks rank
  if let some diagnostic := result.diagnostic then h.diagnostic choice diagnostic
  let some value := result.value | throw (.undefinedBehavior "InvalidUninitBytes")
  pure value

def store (h : AtomicAccessHooks P S C V) (choice : C) (place : V)
    (value : RvalueImmTy P) (ordering : Concurrency.AtomicOrdering) : RvalueM S Unit := do
  -- machine.rs extracts val.to_scalar before converting store ordering.
  let value ← scalar value
  let ordering ← convertOrdering (AtomicWriteOrd.ofOrdering ordering)
  let location ← access h choice place .store
  let previous ← h.ghostRead choice place

  allowDataRaces h (h.physicalWrite choice (.scalar value) place)
  if raceDetecting h (← get) then
    dispatch h location fun state threads => atomicStoreState state threads location.range ordering value previous

def rmwValue [PointerProvenance P] (h : AtomicAccessHooks P S C V) (choice : C)
    (op : IntrinsicAtomicRmw) (left right : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  match op with
  | .mir op negate =>
    let value ← ScalarOps.binary h.scalarOps choice op left right
    if negate then ScalarOps.unary h.scalarOps choice .Not value else pure value
  | .min | .max =>
    let compared ← ScalarOps.binary h.scalarOps choice .Lt left right
    let less ← liftResult ((← scalar compared).toBool |>.mapError ScalarOps.scalarError)
    pure (if op == .min then (if less then left else right) else (if less then right else left))
  | .swap => pure right

def rmw [PointerProvenance P] (h : AtomicAccessHooks P S C V) (choice : C) (place : V)
    (op : IntrinsicAtomicRmw) (operand : RvalueImmTy P)
    (ordering : Concurrency.AtomicOrdering) : RvalueM S (Memory.Scalar P) := do
  let ordering := AtomicRwOrd.ofOrdering ordering
  let location ← access h choice place .rmw
  let old ← allowDataRaces h (h.physicalRead choice place)

  let value ← rmwValue h choice op old operand
  allowDataRaces h (h.physicalWrite choice value.imm place)
  let old ← scalar old
  let value ← scalar value
  if raceDetecting h (← get) then
    dispatch h location fun state threads => atomicRmwState state threads location.range ordering old value
  pure old

def compareExchange [PointerProvenance P] (h : AtomicAccessHooks P S C V) (choice : C)
    (place : V) (expected newValue : RvalueImmTy P) (weak : Bool)
    (success failure : Concurrency.AtomicOrdering) : RvalueM S (Memory.Scalar P × Bool) := do
  -- new.to_scalar precedes ordering conversion at machine.rs boundary.
  let newValue ← scalar newValue
  let success := AtomicRwOrd.ofOrdering success
  let failure ← convertOrdering (AtomicReadOrd.ofOrdering failure)
  let location ← access h choice place .rmw
  let old ← allowDataRaces h (h.physicalRead choice place)

  let equal ← ScalarOps.binary h.scalarOps choice .Eq old expected
  let equal ← liftResult ((← scalar equal).toBool |>.mapError ScalarOps.scalarError)
  let succeeds ← if !equal then pure false else if !weak then pure true else
    match h.weakPolicy with
    | .neverFail => pure true | .alwaysFail => pure false | .mayFail => h.weakSuccessChoice choice
  let old ← scalar old
  if succeeds then
    allowDataRaces h (h.physicalWrite choice (.scalar newValue) place)
    if raceDetecting h (← get) then
      dispatch h location fun state threads => atomicRmwState state threads location.range success old newValue
  else
    -- Miri runs this tail whenever a vector-clock backend exists, even after
    -- the single-thread fast path disables race detection. In that state the
    -- validation transition is a no-op, but SeqCst bookkeeping and an existing
    -- weak-memory buffer's latest-read metadata still belong to the operation.
    if (h.getGlobal (← get)).isSome then
      dispatch h location fun state threads => atomicCompareExchangeFailureState state threads location.range failure
  pure (old, succeeds)

def fence (h : AtomicAccessHooks P S C V) (ordering : Concurrency.AtomicOrdering)
    (singlethread : Bool) : RvalueM S Unit := do
  let ordering ← convertOrdering (prepareAtomicFence ordering singlethread)
  if let some ordering := ordering then
    let state ← get
    let some global := h.getGlobal state | return ()
    if !global.raceDetecting then return ()
    match global.atomicFence (h.threads state) ordering with
    | .ok global => set (h.setGlobal state global)
    | .error error => throw (h.classifyGlobalError error)

/-- Actual Miri operator.rs pointer operations used by atomic pointers. Relative
CTFE provenance cannot be substituted for machine addresses. The arithmetic
branch keeps the source's usize temporary layout while retaining LHS provenance. -/
def pointerBinary [PointerProvenance P] (target : TargetDataLayout)
    (ops : ScalarOpsHooks P S C) (isRaw : C → TyId → RvalueM S Bool)
    (usizeLayout : C → RvalueM S (TyAndLayout TyId)) (choice : C)
    (op : BinOp) (left right : RvalueImmTy P) : RvalueM S (RvalueImmTy P) := do
  let size := Size.fromBits target.pointerWidth.bits
  match op with
  | .Eq | .Ne | .Lt | .Le | .Gt | .Ge =>
    if left.layout.layout.backendRepr != right.layout.layout.backendRepr then invalid "pointer comparison backend mismatch"
    let pair := fun (value : RvalueImmTy P) => do
      match value.imm with
      | .scalar a => pure ((← liftResult (a.toBits size |>.mapError ScalarOps.scalarError)), (0 : U128))
      | .scalarPair a b =>
        let a ← liftResult (a.toBits size |>.mapError ScalarOps.scalarError)
        let b ← liftResult (b.toBits size |>.mapError ScalarOps.scalarError)
        pure (a,b)
      | .uninit => invalid "uninitialized pointer comparison immediate"
    let left ← pair left
    let right ← pair right
    let order := if left.1 == right.1 then compare left.2.toNat right.2.toNat else compare left.1.toNat right.1.toNat
    let result := match op with
      | .Eq => order == .eq | .Ne => order != .eq | .Lt => order == .lt
      | .Le => order != .gt | .Gt => order == .gt | .Ge => order != .lt | _ => false
    pure ⟨.scalar (.fromBool result), ← ops.boolLayout choice⟩
  | .Add | .Sub | .BitOr | .BitAnd | .BitXor =>
    if !(← isRaw choice left.layout.ty) then invalid "atomic pointer arithmetic requires raw pointer"
    let layout ← usizeLayout choice
    if right.layout.ty != layout.ty then invalid "atomic pointer arithmetic RHS must be usize"
    let ptr ← liftResult ((← scalar left).toPointer target |>.mapError ScalarOps.scalarError)
    if !PointerProvenance.offsetIsAddr (Prov := P) then throw (.unsupported "Miri atomic pointer arithmetic requires address provenance")
    let address ← liftResult (Memory.Scalar.fromUInt (BitVec.ofNat 128 ptr.offset.bytes.toNat) layout.layout.size |>.mapError ScalarOps.scalarError)
    let result ← ScalarOps.binary ops choice op ⟨.scalar address, layout⟩ right
    let address ← liftResult ((← scalar result).toTargetUsize size |>.mapError ScalarOps.scalarError)
    let ptr := { ptr with offset := Size.ofBytes address }
    let value ← liftResult (Memory.Scalar.fromMaybePointer target ptr |>.mapError ScalarOps.scalarError)
    pure ⟨.scalar value, layout⟩
  | _ => invalid "unsupported Miri pointer binary operation"

private def rmwName : String → Option IntrinsicAtomicRmw
  | "atomic_or" => some (.mir .BitOr false) | "atomic_xor" => some (.mir .BitXor false)
  | "atomic_and" => some (.mir .BitAnd false) | "atomic_nand" => some (.mir .BitAnd true)
  | "atomic_xadd" => some (.mir .Add false) | "atomic_xsub" => some (.mir .Sub false)
  | "atomic_min" | "atomic_umin" => some .min | "atomic_max" | "atomic_umax" => some .max
  | "atomic_xchg" => some .swap | _ => none

/-- Ordering generic indexes and volatile-constant evaluation match pinned
core atomic.rs. Unknown atomic names preserve the source not-handled result. -/
def eval [PointerProvenance P] (h : IntrinsicAtomicHooks P S C V) (choice : C)
    (name : String) (args : Array (OpTy P)) (dest : V) (ret : Option BasicBlockId) : RvalueM S Bool := do
  if let some operation := rmwName name then
    let typeGenerics := if operation == .min || operation == .max || operation == .swap then 1 else 2
    let ordering ← h.orderingConst choice typeGenerics
    arity args 2
    let place ← h.derefPointer choice (← arg args 0)
    let value ← h.readImmediate choice (← arg args 1)
    let old ← rmw h.toAtomicAccessHooks choice place operation value ordering
    h.writeImmediate choice (.scalar old) dest
  else
    match name with
    | "atomic_load" =>
      let ordering ← h.orderingConst choice 1
      h.volatileConst choice 2
      arity args 1
      let place ← h.derefPointer choice (← arg args 0)
      h.writeImmediate choice (.scalar (← load h.toAtomicAccessHooks choice place ordering)) dest
    | "atomic_store" =>
      let ordering ← h.orderingConst choice 1
      h.volatileConst choice 2
      arity args 2
      let place ← h.derefPointer choice (← arg args 0)
      let value ← h.readImmediate choice (← arg args 1)
      store h.toAtomicAccessHooks choice place value ordering
    | "atomic_cxchg" | "atomic_cxchgweak" =>
      let success ← h.orderingConst choice 1
      let failure ← h.orderingConst choice 2
      arity args 3
      let place ← h.derefPointer choice (← arg args 0)
      let expected ← h.readImmediate choice (← arg args 1)
      let newValue ← h.readImmediate choice (← arg args 2)
      let (old, success) ← compareExchange h.toAtomicAccessHooks choice place expected newValue (name == "atomic_cxchgweak") success failure
      h.writeImmediate choice (.scalarPair old (.fromBool success)) dest
    | "atomic_fence" | "atomic_singlethreadfence" =>
      let ordering ← h.orderingConst choice 0
      arity args 0
      fence h.toAtomicAccessHooks ordering (name == "atomic_singlethreadfence")
    | _ => return false
  h.returnToBlock choice ret
  return true

end IntrinsicAtomic
end Miri.Interpreter
