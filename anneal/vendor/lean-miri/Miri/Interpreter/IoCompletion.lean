import Miri.Interpreter.Files
import Miri.Interpreter.IoCompletionData

/-! Exact source read/write finish captures from unix/fd.rs and windows/fs.rs.
The data is the source FnOnce environment; it is not an instruction language.
Callbacks retain no arbitrary interpreter function in persistent machine state. -/
namespace Miri.Interpreter.IoCompletion
open Miri.ABI Miri.Memory
abbrev Dest := IoCompletionData.Dest
abbrev Buffer := IoCompletionData.Buffer
abbrev Capture := IoCompletionData.Capture
structure Hooks (S E : Type) where
  writeInt : Int → Dest → EStateM StepError S Unit
  writeTargetIsize : Nat → Dest → EStateM StepError S Unit
  errnoNegOne : IoError.Error E → Dest → EStateM StepError S Unit
  deallocateStack : Pointer (Option Provenance) → EStateM StepError S Unit
  offsetInbounds : Pointer (Option Provenance) → Int64 → EStateM StepError S (Pointer (Option Provenance))
  copyNonoverlapping : Pointer (Option Provenance) → Pointer (Option Provenance) → Size → EStateM StepError S Unit
private def invalid (message : String) : EStateM StepError S A := throw (.invalidProgram message)
/-- Readv writes the result before copying/freeing. Writev frees before writing
its result. Failure retains every completed store/copy/free, as in source. -/
def invoke (h : Hooks S E) (capture : Capture) (result : Files.Result E Nat) : EStateM StepError S Unit := do
  match capture with
  | .unixScalar count dest =>
    match result with
    | .ok countRead =>
      if countRead > count then invalid "FD returned more bytes than requested"
      h.writeInt (Int.ofNat countRead) dest
    | .error error => h.errnoNegOne error dest
  | .windowsNt count status information dest =>
    match result with
    | .ok countRead =>
      if countRead > count.toNat then invalid "NtReadFile/NtWriteFile returned more bytes than requested"
      if countRead >= 2^64 then invalid "Windows IO usize-to-u64 conversion panic"
      h.writeInt (Int.ofNat countRead) information
      h.writeInt 0 status
      h.writeInt 0 dest
    | .error error =>
      h.writeInt 0 information
      let code := IoError.intoNtstatus error
      h.writeInt code.toInt status
      h.writeInt code.toInt dest
  | .unixVectored write temporary buffers dest =>
    if write then
      h.deallocateStack temporary
      match result with
      | .ok count => h.writeTargetIsize count dest
      | .error error => h.errnoNegOne error dest
    else
      let count ← match result with
        | .ok count => h.writeTargetIsize count dest; pure (some count)
        | .error error =>
          h.deallocateStack temporary
          h.errnoNegOne error dest
          pure none
      let some count := count | return
      if count >= 2^64 then invalid "source vectored IO usize-to-u64 conversion panic"
      let mut remaining := count
      for (pointer,length) in buffers do
        let copied := count-remaining
        if copied >= 2^63 then invalid "source vectored IO i64 offset conversion panic"
        let source ← h.offsetInbounds temporary (Int64.ofInt (Int.ofNat copied))
        let amount := min length.toNat remaining
        h.copyNonoverlapping source pointer (Size.ofBytes (UInt64.ofNat amount))
        remaining := remaining-amount
        if remaining == 0 then break
      h.deallocateStack temporary
end Miri.Interpreter.IoCompletion
