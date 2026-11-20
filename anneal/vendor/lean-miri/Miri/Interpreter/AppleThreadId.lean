import Miri.Interpreter.UnixThread
import Miri.Interpreter.EnvVars

/-! Pinned unix/env.rs::apple_pthread_threadid_np. The null output test precedes
reading pthread_t; errors return libc scalars and do not dereference the output. -/
namespace Miri.Interpreter.AppleThreadId
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
structure Hooks (S : Type) where
  os : String
  thread : UnixThread.Hooks S
  process : EnvVars.ProcessHooks S
  libc : String → M S (Scalar Provenance)
  u64Layout : M S LocalLayout
  writeInt : Int → MPlaceTy Provenance → M S Unit
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

def query (h : Hooks S) (thread output : OpTy Provenance) : M S (Scalar Provenance) := do
  unless h.os == "macos" do throw (.invalidProgram "Apple pthread thread ID on non-macOS")
  let pointer ← h.thread.readPointer output
  if ← h.thread.isNull pointer then return ← h.libc "EINVAL"
  let value ← h.thread.readScalar thread
  let layout ← h.thread.pthreadLayout
  let raw ← lift (value.toInt layout.layout.size |>.mapError ScalarOps.scalarError)
  let manager ← h.thread.threads
  let id ← if raw == 0 then pure manager.activeThread else do
    if raw < 0 then return ← h.libc "ESRCH"
    match manager.threadIdTryFrom raw.toNat with
    | .ok id => pure id
    | .error _ => return ← h.libc "ESRCH"
  let tid ← EnvVars.getTid h.process (UInt32.ofNat id.toNat)
  let dest ← h.thread.dereference output (← h.u64Layout)
  h.writeInt (Int.ofNat tid.toNat) dest
  lift (Scalar.fromUInt (BitVec.ofNat 128 0) (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
end Miri.Interpreter.AppleThreadId
