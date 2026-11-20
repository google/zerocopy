import Miri.Input.CompilerUnixThread
import Miri.Input.CompilerProviders
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerLibcConstants
import Miri.Interpreter.UnixThreadDispatch

/-! Bind source thread wrappers to canonical compiler signatures and constants;
physical thread, memory, errno and return writes remain runtime operations. -/
namespace Miri.Input.CompilerUnixThreadDispatch
open Miri.Interpreter
private def lift (query : Except String A) : EStateM StepError S A :=
  match query with
  | .ok value => pure value
  | .error error => throw (.unsupported error)

def hooks (p : CompilerProviders.Prepared) (constants : CompilerNamedConstants.Prepared)
    (abis : CompilerNamedShimAbi.Prepared) (base : UnixThreadDispatch.Hooks S D B I) :
    UnixThreadDispatch.Hooks S D B I :=
  {base with
    thread := CompilerUnixThread.hooks p base.thread
    signature := CompilerUnixThread.signature abis
    libc := fun name => lift (CompilerLibcConstants.scalar constants name)
    apple := {base.apple with
      os := base.signatures.os
      thread := CompilerUnixThread.hooks p base.thread
      libc := fun name => lift (CompilerLibcConstants.scalar constants name)
      u64Layout := lift (p.primitiveLayout "u64")}}
end Miri.Input.CompilerUnixThreadDispatch
