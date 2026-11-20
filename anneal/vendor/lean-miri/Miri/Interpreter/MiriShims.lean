import Miri.Interpreter.ForeignItems
import Miri.Interpreter.Unwind
import Miri.Interpreter.ProvenanceGC

/-! Source Miri-specific portable extern arms, foreign_items.rs324-610.
Diagnostics are omitted only after all argument reads/checks; operations that
can affect memory, provenance or control flow remain explicit. Backtrace APIs
and host-path conversion require their actual source implementation.
-/
namespace Miri.Interpreter.MiriShims
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
open ForeignItems (EmulateItemResult)
abbrev M := EStateM StepError

structure Operations (P S D MD B I HostPath : Type) where
  readU64 : OpTy P → M S UInt64
  readU8 : OpTy P → M S UInt8
  readBool : OpTy P → M S Bool
  readImmediate : OpTy P → M S (RvalueImmTy P)
  readByteSlice : RvalueImmTy P → M S ByteArray
  writeU64 : UInt64 → MD → M S Unit
  writeUsize : UInt64 → MD → M S Unit
  writeBool : Bool → MD → M S Unit
  /-- Source ptr_get_alloc_id(ptr,0); errors remain values so selected Miri
  APIs can apply their source Abort conversion while preserving prior effects. -/
  allocation : Pointer (Option P) → M S (Except StepError (AllocId × Size))
  /-- Authoritative numeric rustc `AllocId.0.get()` for this resolved source
  allocation. This must come from the same source identity domain; the
  interpreter's internal/import allocation number is not a substitute. -/
  sourceAllocIdNumber : AllocId → M S UInt64
  allocationInfo : AllocId → M S (Size × Align × AllocationKind)
  localCAllocation : AllocId → M S Bool
  trackAllocation : AllocId → M S Bool
  staticRoot : AllocId → M S Unit
  startUnwind : OpTy P → M S Unit
  provenanceGc : M S Unit
  /-- TB debug naming can reject the requested ancestry; preserve that check. -/
  namePointer : Pointer (Option P) → UInt8 → ByteArray → M S Unit
  /-- The source ABI supplies rustc's raw AllocId number. It must remain raw
  until the source-image witness resolves its identity domain. -/
  printBorrowState : UInt64 → Bool → M S Unit
  checkNoIsolation : String → M S Unit
  readHostPath : Pointer (Option P) → M S HostPath
  writeTargetPath : HostPath → Pointer (Option P) → UInt64 → M S (Bool × UInt64)
  spawnThread : MD → Pointer (Option P) → RvalueImmTy P → M S Unit
  /-- Invalid IDs are None; terminated but existing threads are Some. -/
  threadFromUsize : UInt64 → M S (Option ThreadId)
  joinExclusive : ThreadId → Bool → MD → M S Unit
  yieldThread : M S Unit
  /-- Host stdout/stderr write errors are ignored by Miri, but missing host
  semantics is not an I/O error that may be silently ignored. -/
  writeHost : Bool → ByteArray → M S Unit
  symbolicPromise : Pointer (Option P) → Align → M S Unit

structure CoreHooks (P S D MD B I HostPath : Type) extends Operations P S D MD B I HostPath where
  foreign : ForeignItems.Core P S D MD (Pointer (Option P)) B I

structure Hooks (P S D MD B I HostPath : Type) extends Operations P S D MD B I HostPath where
  foreign : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I

def Hooks.core (h : Hooks P S D MD B I HostPath) : CoreHooks P S D MD B I HostPath :=
  {toOperations := h.toOperations,foreign := h.foreign.toCore}
instance : CoeOut (Hooks P S D MD B I HostPath) (CoreHooks P S D MD B I HostPath) := ⟨Hooks.core⟩

namespace Source
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "Miri shim missing checked argument")
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

private def allocation (h : CoreHooks P S D MD B I HostPath) (pointer : Pointer (Option P))
    (abortOnError : Bool) : M S (AllocId × Size) := do
  match ← h.allocation pointer with
  | .ok value => return value
  | .error error =>
    if abortOnError then throw (.machineStop "pointer passed to miri_get_alloc_id is dangling")
    else throw error

private def signature (name : String) : Option ForeignItems.Signature :=
  if name == "miri_alloc" then some ⟨.Rust,#[.usize,.usize],.unitPointer⟩
  else if name == "miri_dealloc" then some ⟨.Rust,#[.unitPointer,.usize,.usize],.unit⟩
  else if name == "miri_track_alloc" || name == "miri_static_root" then some ⟨.Rust,#[.unitPointer],.unit⟩
  else if name == "miri_start_unwind" then some ⟨.Rust,#[.unitPointer],.never⟩
  else if name == "miri_run_provenance_gc" || name == "miri_spin_loop" then some ⟨.Rust,#[],.unit⟩
  else if name == "miri_get_alloc_id" then some ⟨.Rust,#[.unitPointer],.u64⟩
  else if name == "miri_print_borrow_state" then some ⟨.Rust,#[.u64,.bool],.unit⟩
  else if name == "miri_pointer_name" then some ⟨.Rust,#[.unitPointer,.u8,.byteSlice],.unit⟩
  else if name == "miri_host_to_target_path" then some ⟨.Rust,#[.unitPointer,.unitPointer,.usize],.usize⟩
  else if name == "miri_thread_spawn" then some ⟨.Rust,#[.functionPointer,.unitPointer],.usize⟩
  else if name == "miri_thread_join" then some ⟨.Rust,#[.usize],.bool⟩
  else if name == "miri_write_to_stdout" || name == "miri_write_to_stderr" then some ⟨.Rust,#[.byteSlice],.unit⟩
  else if name == "miri_promise_symbolic_alignment" then some ⟨.Rust,#[.unitPointer,.usize],.unit⟩
  else if name == "malloc_usable_size" then some ⟨.C,#[.pointer],.usize⟩
  else none

def emulate (h : CoreHooks P S D MD B I HostPath) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option EmulateItemResult) := do
  let some signature := signature name | return none
  if name == "malloc_usable_size" then
    unless #["linux","freebsd","android"].contains h.foreign.os do
      throw (.unsupported "malloc_usable_size unavailable on this target OS")
  let f := h.foreign
  let args ← ForeignItems.Core.checkSignature f name signature abi args
  if name == "miri_alloc" then
    let size ← f.readUsize (← arg args 0)
    let alignment ← f.readUsize (← arg args 1)
    let alignment ← lift (ForeignItems.checkRustAllocRequest f.maximumSize size alignment)
    f.writePointer (← f.allocate size alignment .uninit .miri) dest
  else if name == "miri_dealloc" then
    let pointer ← f.readPointer (← arg args 0)
    let size ← f.readUsize (← arg args 1)
    let alignment ← f.readUsize (← arg args 2)
    let alignment ← match Align.fromBytes alignment with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"miri_dealloc alignment unwrap: {reprStr error}")
    f.deallocate pointer (some (size,alignment)) .miri
  else if name == "miri_track_alloc" then
    let (id,_) ← allocation h (← f.readPointer (← arg args 0)) true
    if ← h.trackAllocation id then
      let _ ← h.allocationInfo id
      pure ()
  else if name == "miri_start_unwind" then
    h.startUnwind (← arg args 0)
    return some .NeedsUnwind
  else if name == "miri_run_provenance_gc" then h.provenanceGc
  else if name == "miri_get_alloc_id" then
    let (id,_) ← allocation h (← f.readPointer (← arg args 0)) true
    let number ← h.sourceAllocIdNumber id
    h.writeU64 number dest
  else if name == "miri_print_borrow_state" then
    let raw ← h.readU64 (← arg args 0)
    let showUnnamed ← h.readBool (← arg args 1)
    h.printBorrowState raw showUnnamed
  else if name == "miri_pointer_name" then
    let pointer ← f.readPointer (← arg args 0)
    let parent ← h.readU8 (← arg args 1)
    let bytes ← h.readByteSlice (← h.readImmediate (← arg args 2))
    -- namePointer must use source from_utf8_lossy when its diagnostic name is stored.
    h.namePointer pointer parent bytes
  else if name == "miri_static_root" then
    let (id,offset) ← allocation h (← f.readPointer (← arg args 0)) false
    if offset != .ZERO then throw (.unsupported "miri_static_root pointer must be allocation start")
    h.staticRoot id
  else if name == "miri_host_to_target_path" then
    let pointer ← f.readPointer (← arg args 0)
    let output ← f.readPointer (← arg args 1)
    let size ← f.readUsize (← arg args 2)
    h.checkNoIsolation "miri_host_to_target_path"
    let path ← h.readHostPath pointer
    let (success,needed) ← h.writeTargetPath path output size
    h.writeUsize (if success then 0 else needed) dest
  else if name == "miri_thread_spawn" then
    let routine ← f.readPointer (← arg args 0)
    let argument ← h.readImmediate (← arg args 1)
    h.spawnThread dest routine argument
  else if name == "miri_thread_join" then
    let raw ← f.readUsize (← arg args 0)
    match ← h.threadFromUsize raw with
    | none => h.writeBool false dest
    | some thread => h.joinExclusive thread true dest
  else if name == "miri_spin_loop" then h.yieldThread
  else if name == "miri_write_to_stdout" || name == "miri_write_to_stderr" then
    let bytes ← h.readByteSlice (← h.readImmediate (← arg args 0))
    h.writeHost (name == "miri_write_to_stderr") bytes
  else if name == "miri_promise_symbolic_alignment" then
    let pointer ← f.readPointer (← arg args 0)
    let requested ← f.readUsize (← arg args 1)
    if requested == 0 || (requested &&& (requested-1)) != 0 then
      throw (.unsupported "miri_promise_symbolic_alignment requires power of two")
    let alignment ← match Align.fromBytes requested with
      | .ok value => pure value
      | .error (.tooLarge _) => pure Align.MAX
      | .error _ => throw (.invalidProgram "power-of-two alignment conversion")
    let bytes ← match alignment.bytes with
      | .ok bytes => pure bytes
      | .error error => throw (.invalidProgram s!"promised alignment: {reprStr error}")
    unless pointer.offset.bytes % bytes == 0 do
      throw (.unsupported "miri_promise_symbolic_alignment pointer is not actually aligned")
    h.symbolicPromise pointer alignment
  else
    let pointer ← f.readPointer (← arg args 0)
    let size : Size ← if ← f.isNull pointer then pure Size.ZERO else do
      let (id,offset) ← allocation h pointer false
      unless offset == .ZERO do throw (.undefinedBehavior "malloc_usable_size pointer is not allocation start")
      unless ← h.localCAllocation id do throw (.undefinedBehavior "malloc_usable_size pointer is not C-managed memory")
      pure (← h.allocationInfo id).1
    h.writeUsize size.bytes dest
  return some .NeedsReturn

end Source

def emulate (h : Hooks P S D MD B I HostPath) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option EmulateItemResult) := Source.emulate h.core name abi args dest

def bind (h : Hooks P S D MD B I HostPath) :
    ForeignItems.Hooks P S D MD (Pointer (Option P)) B I :=
  { h.foreign with otherPortable := fun name abi args dest => do
      if let some result ← Source.emulate h.core name abi args dest then return some result
      h.foreign.otherPortable name abi args dest }

end Miri.Interpreter.MiriShims
