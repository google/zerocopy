import Miri.Interpreter.Constant
import Miri.Concurrency.Thread
import Miri.Memory.MiriMemoryKind

/-! Pinned Miri thread.rs::get_or_create_thread_local_alloc. The actual manager
TLS map remains authoritative; a typed side table supplies its opaque pointer
tokens. Allocation copying, relocation adjustment, mutability, fresh identity,
kind, insertion hooks and failure-state ordering follow the source. Host byte
storage and compiler queries are required leaves, not successful defaults.
-/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency

inductive ThreadLocalError where
  | query (message : String)
  | foreignStatic (definition : MIR.DefId)
  | allocationAdjustment (error : AllocationAdjustError ThreadLocalError)
  | insertion (error : MemoryLifecycleError)
  | missingPointerToken (token : Nat)
  | duplicateTlsEntry
  | pointerIdentityMismatch
  | changedByteCopy
  deriving Repr

structure ThreadLocalEntry (P : Type) where
  definition : MIR.DefId
  thread : ThreadId
  runtimeId : AllocId
  pointer : Pointer P

structure ThreadLocalState (P E H : Type) where
  memory : MemoryState P E MiriMemoryKind
  hooks : H
  manager : ThreadManager
  pointers : Array (ThreadLocalEntry P)

abbrev ThreadLocalM (P E H A : Type) := EStateM ThreadLocalError (ThreadLocalState P E H) A

structure ThreadLocalQueries (P E H Params : Type) where
  isForeignItem : MIR.DefId → ThreadLocalM P E H Bool
  defaultAllocationParams : ThreadLocalM P E H Params
  evaluateStaticInitializer : MIR.DefId → ThreadLocalM P E H (Allocation CtfeProvenance Unit)
  copyBytes : Params → Array UInt8 → Align → ThreadLocalM P E H (Array UInt8)
  globalRootPointer : Pointer CtfeProvenance → ThreadLocalM P E H (Pointer P)
  /-- Source max_size_of_val query, including any machine-specific limit. -/
  maximumAllocationSize : ThreadLocalM P E H Size
  globalKind : Option (MemoryKind MiriMemoryKind)
  synchronizeMemory : MemoryState P E MiriMemoryKind → H → H
  initExtra : MemoryState P E MiriMemoryKind → H → AllocId → MemoryKind MiriMemoryKind →
    Size → Align → MemoryStateHookResult P E MiriMemoryKind H E
  adjustAllocationRoot : MemoryState P E MiriMemoryKind → H → AllocId →
    MemoryKind MiriMemoryKind → MemoryStateHookResult P E MiriMemoryKind H (Pointer P)

/-- Recover real pointers for the existing thread manager's TLS visitation and
cleanup protocol. A missing typed token is an obligation, never a dropped root. -/
def ThreadLocalState.pointerForToken (state : ThreadLocalState P E H) (token : Nat) :
    Except ThreadLocalError (Pointer P) := do
  let some entry := state.pointers.find? (fun entry => entry.runtimeId.value.toNat == token)
    | throw (.missingPointerToken token)
  pure entry.pointer

def ThreadLocalState.roots (state : ThreadLocalState P E H) : Except ThreadLocalError (Array (Pointer P)) := do
  state.manager.threadLocalAllocs.toArray.mapM fun entry => do
    let some pointer := state.pointers.find? (fun pointer => pointer.runtimeId.value.toNat == entry.pointerToken)
      | throw (.missingPointerToken entry.pointerToken)
    unless pointer.definition == entry.definitionToken && pointer.thread == entry.thread do
      throw .pointerIdentityMismatch
    pure pointer.pointer

/-- The cached branch performs no compiler query or machine allocation work.
The new branch copies first, then makes the allocation mutable and inserts it
as MiriMemoryKind::Tls. Only successful root adjustment publishes the TLS map
entry; failures retain any earlier allocation and hook state changes. -/
def getOrCreateThreadLocal [PointerProvenance P] (target : RuntimeTargetDataLayout)
    (queries : ThreadLocalQueries P E H Params) (definition : MIR.DefId) :
    ThreadLocalM P E H (Pointer P) := do
  let before ← EStateM.get
  let thread := before.manager.activeThread
  if let some cached := before.manager.threadLocalAllocs.find? (fun entry => entry.definitionToken == definition && entry.thread == thread) then
    let some entry := before.pointers.find? (fun entry => entry.runtimeId.value.toNat == cached.pointerToken)
      | throw (.missingPointerToken cached.pointerToken)
    unless entry.definition == definition && entry.thread == thread do throw .pointerIdentityMismatch
    match before.pointerForToken cached.pointerToken with
    | .ok pointer => return pointer
    | .error error => throw error
  if before.pointers.any (fun entry => entry.definition == definition && entry.thread == thread) then
    throw .duplicateTlsEntry
  if ← queries.isForeignItem definition then throw (.foreignStatic definition)
  let params ← queries.defaultAllocationParams
  let source ← queries.evaluateStaticInitializer definition
  let copied ← fun state =>
    match Allocation.adjustFromTcx source target.base
        (fun bytes align => fun state =>
          match queries.copyBytes params bytes align state with
          | .ok copied next => if copied == bytes then .ok copied next else .error .changedByteCopy next
          | .error error next => .error error next)
        queries.globalRootPointer state with
    | .ok allocation next => .ok allocation next
    | .error error next => .error (.allocationAdjustment error) next
  let mutableCopy := copied.withMutability .Mut
  let maximum ← queries.maximumAllocationSize
  let ready ← EStateM.get
  let expectedId := ready.memory.nextAllocId
  let inserted := MemoryLifecycle.insertAllocation ready.memory ready.hooks queries.synchronizeMemory mutableCopy
    (.machine .tls) maximum queries.globalKind queries.initExtra queries.adjustAllocationRoot
  EStateM.set { ready with memory := inserted.memory, hooks := inserted.hooks }
  let pointer ← match inserted.outcome with
    | .ok pointer => pure pointer
    | .error error => throw (.insertion error)
  let some id := PointerProvenance.getAllocId pointer.provenance | throw .pointerIdentityMismatch
  unless id.value == expectedId do throw .pointerIdentityMismatch
  let after ← EStateM.get
  let thread := after.manager.activeThread
  if after.manager.threadLocalAllocs.any (fun entry => entry.definitionToken == definition && entry.thread == thread) then
    throw .duplicateTlsEntry
  let manager := { after.manager with threadLocalAllocs :=
    after.manager.threadLocalAllocs ++ [⟨definition, thread, id.value.toNat⟩] }
  EStateM.set { after with manager := manager, pointers := after.pointers.push ⟨definition, thread, id, pointer⟩ }
  pure pointer

end Miri.Interpreter
