import Miri.Interpreter.UnixMemory

/-! Entire pinned unix/linux/mem.rs: restricted mremap with actual zeroed
reallocation semantics, not the common realloc callback's Uninit policy. -/
namespace Miri.Interpreter.LinuxMemory
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S Place B I : Type) where
  memory : UnixMemory.Hooks Provenance S Place (MPlaceTy Provenance) B I
  reallocateZero : Pointer (Option Provenance) → Size → Size → Align → M S (Pointer (Option Provenance))

def remap (h : Hooks S Place B I) (address oldSize newSize flags : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let pointer ← h.memory.foreign.readPointer address
  let oldSize ← h.memory.foreign.readUsize oldSize
  let newSize ← h.memory.foreign.readUsize newSize
  let flags ← h.memory.foreign.readI32 flags
  let fail := do
    h.memory.setErrno "EINVAL"
    h.memory.writeScalar (← h.memory.mapFailed) dest
  if h.memory.pageSize == 0 then throw (.invalidProgram "mremap zero machine page size")
  if pointer.offset.bytes % h.memory.pageSize != 0 || newSize == 0 then
    fail
    return
  if flags &&& (← h.memory.libcI32 "MREMAP_FIXED") != 0 then throw (.unsupported "mremap MREMAP_FIXED")
  if flags &&& (← h.memory.libcI32 "MREMAP_DONTUNMAP") != 0 then throw (.unsupported "mremap MREMAP_DONTUNMAP")
  if flags &&& (← h.memory.libcI32 "MREMAP_MAYMOVE") == 0 then
    fail
    return
  let align ← match Align.fromBytes h.memory.pageSize with
    | .ok value => pure value | .error error => throw (.invalidProgram s!"machine page alignment: {reprStr error}")
  let pointer ← h.reallocateZero pointer (Size.ofBytes oldSize) (Size.ofBytes newSize) align
  h.memory.foreign.writePointer pointer dest
end Miri.Interpreter.LinuxMemory
