import Miri.Interpreter.ForeignItems
import Miri.Memory.Pointer

/-! Entire pinned unix/mem.rs plus posix_memalign/aligned_alloc/reallocarray
source policy. Miri's deliberately restricted mmap is preserved: unsupported
mapping modes are not replaced with successful anonymous allocations.
-/
namespace Miri.Interpreter.UnixMemory
open Miri.ABI Miri.Memory Miri.MIR
open ForeignItems (EmulateItemResult)
abbrev M := EStateM StepError
structure Hooks (P S D MD B I : Type) where
  foreign : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I
  pointerSize : UInt64
  pageSize : UInt64
  targetIsizeMax : UInt64
  frameInStd : M S Bool
  libcI32 : String → M S Int32
  setErrno : String → M S Unit
  mapFailed : M S (Scalar P)
  writeScalar : Scalar P → MD → M S Unit
  writeI32 : Int32 → MD → M S Unit
  /-- Actual deref_pointer_as(memptr, machine.layouts.unit_ptr_mut). -/
  derefPointerOutput : OpTy P → M S MD
  /-- Compiler-generated exact libc off_t signature/query; no host type alias. -/
  expectedAbi : String → M S (FnAbi TyId)
  readOffset : OpTy P → M S Int
  /-- A returned error is an actual source pointer-access failure. Missing
  metadata/environment must throw an explicit unresolved operation instead. -/
  checkAccess : Pointer (Option P) → UInt64 → M S (Except Unit Unit)

private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "Unix memory shim missing checked argument")
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def unwrapAlign (value : UInt64) : M S Align :=
  match Align.fromBytes value with
  | .ok value => pure value
  | .error error => throw (.invalidProgram s!"source alignment unwrap: {reprStr error}")

private def roundToPage (h : Hooks P S D MD B I) (length : UInt64) : Except StepError (Option UInt64) := do
  if h.pageSize == 0 then throw (.invalidProgram "checked_next_multiple_of zero page size")
  let size := ((length.toNat+h.pageSize.toNat-1)/h.pageSize.toNat)*h.pageSize.toNat
  return if size < 2^64 && size <= h.targetIsizeMax.toNat then some (UInt64.ofNat size) else none
private def pageAligned (h : Hooks P S D MD B I) (pointer : Pointer (Option P)) : Bool :=
  if h.pageSize == 0 then pointer.offset.bytes == 0 else pointer.offset.bytes % h.pageSize == 0
private def errnoReturn (h : Hooks P S D MD B I) (error : String) (dest : MD) : M S Unit := do
  h.setErrno error
  h.writeI32 (-1) dest
private def mapFailure (h : Hooks P S D MD B I) (dest : MD) : M S Unit := do
  h.setErrno "EINVAL"
  h.writeScalar (← h.mapFailed) dest
private def verifyProt (h : Hooks P S D MD B I) (protection : Int32) : M S Unit := do
  let read ← h.libcI32 "PROT_READ"
  let write ← h.libcI32 "PROT_WRITE"
  unless protection == (read ||| write) do
    throw (.unsupported "mmap/mprotect supports only PROT_READ|PROT_WRITE")

/-- Offset is read by the foreign dispatcher BEFORE any other mmap argument. -/
def mmap (h : Hooks P S D MD B I) (args : Array (OpTy P)) (offset : Int) (dest : MD) : M S Unit := do
  let f := h.foreign
  let address ← f.readUsize (← arg args 0)
  let length ← f.readUsize (← arg args 1)
  let protection ← f.readI32 (← arg args 2)
  let flags ← f.readI32 (← arg args 3)
  let fd ← f.readI32 (← arg args 4)
  let privateFlag ← h.libcI32 "MAP_PRIVATE"
  let anonymous ← h.libcI32 "MAP_ANONYMOUS"
  let shared ← h.libcI32 "MAP_SHARED"
  let fixed ← h.libcI32 "MAP_FIXED"
  let inStd ← h.frameInStd
  if inStd && #["macos","solaris","illumos"].contains f.os && (flags &&& fixed) != 0 then
    f.writePointer (Pointer.withoutProvenance address) dest
    return
  let selection := (flags &&& (privateFlag ||| shared)).toUInt32
  if selection == 0 || (selection &&& (selection-1)) != 0 then
    mapFailure h dest
    return
  if length == 0 then mapFailure h dest; return
  unless fd == -1 do throw (.unsupported "file-backed mmap unsupported by pinned Miri")
  if (flags &&& fixed) != 0 then throw (.unsupported "MAP_FIXED unsupported by pinned Miri")
  verifyProt h protection
  unless flags == (privateFlag ||| anonymous) do throw (.unsupported "mmap requires exactly MAP_PRIVATE|MAP_ANONYMOUS")
  unless offset == 0 do throw (.unsupported "nonzero mmap offset unsupported by pinned Miri")
  let alignment ← unwrapAlign h.pageSize
  let some length ← lift (roundToPage h length) | mapFailure h dest; return
  f.writePointer (← f.allocate length alignment .zero .mmap) dest

def munmap (h : Hooks P S D MD B I) (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let address ← h.foreign.readPointer (← arg args 0)
  let length ← h.foreign.readUsize (← arg args 1)
  unless pageAligned h address do errnoReturn h "EINVAL" dest; return
  let some length ← lift (roundToPage h length) | errnoReturn h "EINVAL" dest; return
  let alignment ← unwrapAlign h.pageSize
  h.foreign.deallocate address (some (length,alignment)) .mmap
  h.writeI32 0 dest

def mprotect (h : Hooks P S D MD B I) (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let address ← h.foreign.readPointer (← arg args 0)
  let length ← h.foreign.readUsize (← arg args 1)
  let protection ← h.foreign.readI32 (← arg args 2)
  unless pageAligned h address do errnoReturn h "EINVAL" dest; return
  verifyProt h protection
  let some length ← lift (roundToPage h length) | errnoReturn h "ENOMEM" dest; return
  match ← h.checkAccess address length with
  | .error () => throw (.undefinedBehavior "mprotect called on out-of-bounds memory")
  | .ok () => h.writeI32 0 dest

def madvise (h : Hooks P S D MD B I) (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let address ← h.foreign.readPointer (← arg args 0)
  let length ← h.foreign.readUsize (← arg args 1)
  let advice ← h.foreign.readI32 (← arg args 2)
  unless pageAligned h address do errnoReturn h "EINVAL" dest; return
  let normal ← h.libcI32 "MADV_NORMAL"
  let random ← h.libcI32 "MADV_RANDOM"
  let sequential ← h.libcI32 "MADV_SEQUENTIAL"
  let willNeed ← h.libcI32 "MADV_WILLNEED"
  unless advice == normal || advice == random || advice == sequential || advice == willNeed do
    throw (.unsupported "unsupported madvise advice")
  let some length ← lift (roundToPage h length) | errnoReturn h "ENOMEM" dest; return
  match ← h.checkAccess address length with
  | .error () => throw (.undefinedBehavior "madvise called on out-of-bounds memory")
  | .ok () => h.writeI32 0 dest

/-- POSIX invalid alignment returns EINVAL without setting errno. Dereference
of the pointer-output operand precedes scalar alignment/size reads. -/
def posixMemalign (h : Hooks P S D MD B I)
    (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let output ← h.derefPointerOutput (← arg args 0)
  let alignment ← h.foreign.readUsize (← arg args 1)
  let size ← h.foreign.readUsize (← arg args 2)
  if alignment == 0 || (alignment &&& (alignment-1)) != 0 || alignment < h.pointerSize then
    h.writeI32 (← h.libcI32 "EINVAL") dest
  else
    let pointer ← h.foreign.allocate size (← unwrapAlign alignment) .uninit .c
    h.foreign.writePointer pointer output
    h.writeI32 0 dest

def alignedAlloc (h : Hooks P S D MD B I) (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let alignment ← h.foreign.readUsize (← arg args 0)
  let size ← h.foreign.readUsize (← arg args 1)
  if alignment != 0 && size % alignment == 0 && (alignment &&& (alignment-1)) == 0 then
    let minimum ← lift (ForeignItems.mallocAlign h.foreign.arch h.foreign.os size)
    let minimum ← match minimum.bytes with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"malloc alignment: {reprStr error}")
    let alignment ← unwrapAlign (max alignment minimum)
    h.foreign.writePointer (← h.foreign.allocate size alignment .uninit .c) dest
  else h.foreign.writeNull dest

def reallocarray (h : Hooks P S D MD B I) (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let pointer ← h.foreign.readPointer (← arg args 0)
  let count ← h.foreign.readUsize (← arg args 1)
  let size ← h.foreign.readUsize (← arg args 2)
  let total := count.toNat*size.toNat
  if total > h.targetIsizeMax.toNat || total >= 2^64 then
    h.foreign.setEnomem
    h.foreign.writeNull dest
  else
    let total := UInt64.ofNat total
    let alignment ← lift (ForeignItems.mallocAlign h.foreign.arch h.foreign.os total)
    let pointer ← if ← h.foreign.isNull pointer then h.foreign.allocate total alignment .uninit .c
      else if total == 0 then throw (.undefinedBehavior "realloc with zero size")
      else h.foreign.reallocate pointer none total alignment .c
    h.foreign.writePointer pointer dest

private def checkedArgs (h : Hooks P S D MD B I) (name : String)
    (abi : FnAbi TyId) (args : Array (OpTy P)) (count : Nat) : M S (Array (OpTy P)) := do
  let callee ← h.expectedAbi name
  unless !callee.cVariadic && callee.args.size == count do
    throw (.invalidProgram "Unix memory source signature query mismatch")
  ForeignItems.checkAbi h.foreign abi callee
  h.foreign.checkSymbolClash name
  unless args.size == count do throw (.invalidProgram "Unix memory shim checked argument count")
  args.mapIdxM fun index value => do
    let expected ← arg callee.args index
    h.foreign.transmute value expected.layout

/-- The Unix foreign-item wrapper controls arity/type checks and off_t reading.
Availability checks occur before the signature query where source does so. -/
def emulate (h : Hooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option EmulateItemResult) := do
  let count := if name == "mmap" then some 6
    else if name == "munmap" || name == "aligned_alloc" then some 2
    else if #["mprotect","madvise","posix_memalign","reallocarray"].contains name then some 3
    else none
  let some count := count | return none
  if name == "reallocarray" then
    unless #["linux","freebsd","android"].contains h.foreign.os do
      throw (.unsupported "reallocarray unavailable on this target OS")
  let args ← checkedArgs h name abi args count
  if name == "mmap" then
    let offset ← h.readOffset (← arg args 5)
    mmap h args offset dest
  else if name == "munmap" then munmap h args dest
  else if name == "mprotect" then mprotect h args dest
  else if name == "madvise" then madvise h args dest
  else if name == "posix_memalign" then posixMemalign h args dest
  else if name == "aligned_alloc" then alignedAlloc h args dest
  else reallocarray h args dest
  return some .NeedsReturn

def bindUnix (h : Hooks P S D MD B I) :
    ForeignItems.Hooks P S D MD (Pointer (Option P)) B I :=
  { h.foreign with unix := fun name abi args dest => do
      if let some result ← emulate h name abi args dest then return result
      h.foreign.unix name abi args dest }

end Miri.Interpreter.UnixMemory
