import Miri.Interpreter.UnixFd
import Miri.Interpreter.ArrayProjection

/-! Entire unix/fd.rs readv/writev policy. IO executes once against a temporary
Stack allocation. Return/copy/free/error order is significant and retained. -/
namespace Miri.Interpreter.UnixVectored
open Miri.ABI Miri.Memory Miri.MIR Files
abbrev M := EStateM StepError
structure Hooks (S H D O E Meta : Type) where
  fd : UnixFd.Hooks S H D O E Meta
  readI32 : OpTy Provenance → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readSigned : OpTy Provenance → M S Int
  arrayPlace : Pointer (Option Provenance) → UInt64 → M S (MPlaceTy Provenance)
  startArray : MPlaceTy Provenance → M S ArrayProjection.Iterator
  index : ArrayProjection.Iterator → Nat → M S (MPlaceTy Provenance)
  field : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  readFieldSigned : MPlaceTy Provenance → M S Int
  readFieldPointer : MPlaceTy Provenance → M S (Pointer (Option Provenance))
  allocateStack : Size → M S (Pointer (Option Provenance))
  deallocateStack : Pointer (Option Provenance) → M S Unit
  offsetInbounds : Pointer (Option Provenance) → Int64 → M S (Pointer (Option Provenance))
  copyNonoverlapping : Pointer (Option Provenance) → Pointer (Option Provenance) → Size → M S Unit
  writeTargetIsize : Nat → MPlaceTy Provenance → M S Unit
  hostUsizeBits : Nat
  /-- Source host build's ordinary-add overflow setting, not the MIR flag. -/
  checkedSum : Bool
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state =>
    match cleanup state with
    | .ok _ state => .error error state
    | .error next state => .error next state
private def u64 (value : Int) : M S UInt64 := do
  if value < 0 || value >= 2^64 then throw (.invalidProgram "source vectored IO u64 conversion panic")
  return UInt64.ofNat value.toNat
private def offset (value : Nat) : M S Int64 := do
  if value >= 2^63 then throw (.invalidProgram "source vectored IO i64 offset conversion panic")
  return Int64.ofInt (Int.ofNat value)
private def buffers (h : Hooks S H D O E Meta) (pointer : Pointer (Option Provenance))
    (count : UInt64) : M S (Array (Pointer (Option Provenance) × UInt64)) := do
  let place ← h.arrayPlace pointer count
  let iterator ← h.startArray place
  let mut result := #[]
  for index in [:iterator.length.toNat] do
    let iovec ← h.index iterator index
    let length ← u64 (← h.readFieldSigned (← h.field iovec "iov_len"))
    let pointer ← h.readFieldPointer (← h.field iovec "iov_base")
    result := result.push (pointer,length)
  return result
private def total (h : Hooks S H D O E Meta)
    (buffers : Array (Pointer (Option Provenance) × UInt64)) : M S UInt64 := do
  let mut result : UInt64 := 0
  for (_,length) in buffers do
    if h.checkedSum && result.toNat+length.toNat >= 2^64 then
      throw (.invalidProgram "source vectored IO ordinary u64 sum overflow panic")
    result := result+length
  return result

def execute (h : Hooks S H D O E Meta) (fd iov count : OpTy Provenance)
    (position : Option (OpTy Provenance)) (write : Bool) (dest : MPlaceTy Provenance) : M S Unit := do
  let number ← h.readI32 fd
  let pointer ← h.readPointer iov
  let count ← u64 (← h.readI32 count).toInt
  let position ← match position with
    | none => pure none
    | some value => do
      if h.fd.os == "solaris" then throw (.unsupported "Solaris positional vectored IO")
      pure (some (← h.readSigned value))
  let some reference := (← h.fd.table).get number
    | IoError.setErrnoAndReturnNeg1 h.fd.errors (.libc "EBADF") dest; return
  let reference ← h.fd.cloneRef reference
  let (buffers,temporary,size) ← onError (do
    let buffers ← buffers h pointer count
    let size ← total h buffers
    let temporary ← h.allocateStack (Size.ofBytes size)
    if write then
      let mut copied : Nat := 0
      for (pointer,length) in buffers do
        let target ← h.offsetInbounds temporary (← offset copied)
        h.copyNonoverlapping pointer target (Size.ofBytes length)
        copied := copied+length.toNat
        if copied >= 2^64 then throw (.invalidProgram "source vectored IO strict_add overflow panic")
    -- Source converts only after allocation, and after copies on writev.
    if size.toNat >= 2^h.hostUsizeBits then throw (.invalidProgram "source vectored IO usize conversion panic")
    pure (buffers,temporary,size)
  ) (h.fd.dropRef reference)
  UnixFd.transferDescription h.fd reference temporary size.toNat position write
    (IoCompletionData.Finish.source (.unixVectored write temporary buffers dest) fun result => do
    if write then
      h.deallocateStack temporary
      match result with
      | .ok size => h.writeTargetIsize size dest
      | .error error => IoError.setErrnoAndReturnNeg1 h.fd.errors error dest
    else
      let size ← match result with
        | .ok size => h.writeTargetIsize size dest; pure size
        | .error error =>
          h.deallocateStack temporary
          IoError.setErrnoAndReturnNeg1 h.fd.errors error dest
          return
      if size >= 2^64 then throw (.invalidProgram "source vectored IO usize-to-u64 conversion panic")
      let mut remaining := size
      for (pointer,length) in buffers do
        let source ← h.offsetInbounds temporary (← offset (size-remaining))
        let amount := min length.toNat remaining
        h.copyNonoverlapping source pointer (Size.ofBytes (UInt64.ofNat amount))
        remaining := remaining-amount
        if remaining == 0 then break
      h.deallocateStack temporary)
end Miri.Interpreter.UnixVectored
