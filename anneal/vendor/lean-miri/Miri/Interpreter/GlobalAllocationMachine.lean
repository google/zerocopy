import Miri.Interpreter.MemoryExtras

/-! Lazy compiler-global conversion, pinned machine.rs:967–1032,1678–1693.
Byte backing is acquired before relocation conversion. Global race clocks start
at zero on the main thread, independently of the accessing thread. The returned
owned allocation is cached by MemoryLifecycle, never by this callback. -/
namespace Miri.Interpreter.GlobalAllocationMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Concurrency

abbrev M := PlaceMachine.MachineM

/-- Real storage effects; native preparation must reserve the actual backing
identity used by global-root address resolution. Managed storage explicitly
returns no host owner. Release runs on failed conversion, like Rust's drop. -/
structure Bytes (K U : Type) where
  prepare : AllocId → Array UInt8 → Align → M K U (Array UInt8 × Option NativeBufferOwnership)
  commit : NativeBufferOwnership → Array UInt8 → Align → M K U Unit
  release : NativeBufferOwnership → Size → Align → M K U Unit

/-- The managed backend's semantic bytes have no native ownership. Receiving
a native owner here is an inconsistent backend construction, not a no-op. -/
def managedBytes : Bytes K U where
  prepare := fun _ bytes _ => pure (bytes,none)
  commit := fun _ _ _ => throw (.invalidProgram "managed globals cannot commit native backing")
  release := fun _ _ _ => throw (.invalidProgram "managed globals cannot drop native backing")

structure Leaves (K U : Type) where
  bytes : Bytes K U
  globalRootPointer : Pointer CtfeProvenance → M K U (Pointer Provenance)
  diagnostic : AllocId → Size → Align → M K U Unit

def initExtra [DecidableEq K] (extras : MemoryExtras.Hooks K U P)
    (diagnostic : AllocId → Size → Align → M K U Unit)
    (id : AllocId) (size : Size) (align : Align) : M K U BorrowTree := do
  diagnostic id size align
  let machine ← get
  let tag ← match machine.borrowTracker with
    | none => pure BorTag.one
    | some tracker =>
      match tracker.global.rootPointerTag id with
      | .error error => throw (.resourceExhaustion s!"global allocation root tag: {reprStr error}")
      | .ok (global,tag) =>
        modify fun machine => {machine with borrowTracker := some {tracker with global}}
        pure tag
  let tree := BorrowTree.new tag size
  if let some global := (← get).dataRace then
    let index ← match global.activeThreadIndex {machine.threads with activeThread := .MAIN_THREAD} with
      | .ok index => pure index
      | .error error => throw (.invalidProgram s!"global allocation main-thread clocks: {reprStr error}")
    let length := ByteSize.ofU64 size.bytes.toNat (by have h := UInt64.toNat_lt size.bytes; omega)
    let allocation := VClockAlloc.newAllocation length VTimestamp.ZERO index
    modify fun machine => {machine with raceAllocations :=
      (machine.raceAllocations.filter fun entry => entry.1 != id).push (id,allocation)}
  let weak := ((← get).dataRace.map (·.weakMemory)).getD false
  MemoryExtras.initAllocation extras id weak
  pure tree

/-- Global and TLS kinds share this source zero/main-thread race category;
both may leak and neither stores an allocation span (machine.rs:222–239). -/
def init [DecidableEq K] (extras : MemoryExtras.Hooks K U P) (leaves : Leaves K U)
    (id : AllocId) (size : Size) (align : Align) : M K U BorrowTree :=
  initExtra extras leaves.diagnostic id size align

def adjust [DecidableEq K] (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : Leaves K U) (id : AllocId) (source : Allocation CtfeProvenance Unit) :
    M K U (AdjustedGlobalAllocation Provenance BorrowTree) := do
  let sourceBytes ← match source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len with
    | .ok bytes => pure bytes
    | .error error => throw (.callback s!"global allocation byte inspection: {reprStr error}")
  let (bytes,owner) ← leaves.bytes.prepare id sourceBytes source.align
  try
    let converted ← fun machine =>
      match Allocation.adjustFromTcx source target
          (fun _ _ state => .ok bytes state) leaves.globalRootPointer machine with
      | .ok allocation machine => .ok allocation machine
      | .error (.byteConversion error) machine | .error (.pointerAdjustment error) machine =>
        .error error machine
      | .error (.allocation error) machine =>
        .error (.callback s!"global allocation conversion: {reprStr error}") machine
    if let some owner := owner then
      let bytes ← match converted.inspectWithUninitAndPtrOutsideInterpreter 0 converted.len with
        | .ok bytes => pure bytes
        | .error error => throw (.callback s!"global allocation converted byte inspection: {reprStr error}")
      leaves.bytes.commit owner bytes converted.align
    let tree ← init extras leaves id converted.byteSize converted.align
    let converted := converted.mapExtra (fun _ => tree)
    let converted ← match owner with
      | none => pure converted
      | some owner => match converted.attachNativeBuffer owner with
        | .ok allocation => pure allocation
        | .error reason => do
          modify (MemoryExtras.discardUninserted extras id)
          throw (.invalidProgram s!"global allocation backing: {reason}")
    pure (.owned converted)
  catch error =>
    if let some owner := owner then leaves.bytes.release owner source.byteSize source.align
    throw error

private def bridge (memory : MemoryState Provenance BorrowTree K)
    (state : PlaceMachine.AccessState K U) (action : M K U A) :
    GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) A :=
  match action {state.machine with memory} with
  | .ok value machine => ⟨machine.memory,{state with machine},.ok value⟩
  | .error error machine => ⟨machine.memory,⟨machine,some error⟩,.error (reprStr error)⟩

def hooks [DecidableEq K] (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit)) :
    GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U) where
  synchronizeMemory := fun memory state => {state with machine := {state.machine with memory}}
  evaluateStaticInitializer := initializer
  -- rustc Machine::before_access_global default; Miri has no override.
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory,state,.ok ()⟩
  adjustGlobalAllocation := fun memory state id source => bridge memory state (adjust target extras leaves id source)

/-- Driver used by ensureTreeExtra. It follows the same lazy conversion/cache
path as ordinary reads; typed callback failures survive the string boundary. -/
def ensure [DecidableEq K] (globalKind : K)
    (hooks : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (id : AllocId) : MachineHooks.M K U Unit := do
  let state ← get
  let result := MemoryLifecycle.getAllocRaw state.machine.memory ⟨state.machine,none⟩ id (some globalKind) hooks
  modify fun state => {state with machine := {result.hooks.machine with memory := result.memory}}
  match result.outcome with
  | .ok _ => pure ()
  | .error error => throw (result.hooks.pendingError.getD
      (.callback s!"global allocation access: {reprStr error}"))
end Miri.Interpreter.GlobalAllocationMachine
