import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedShimAbi
import Miri.ABI.ExternAbi
import Miri.Interpreter.UnixThread

/-! `unix/thread.rs` compiler leaves. libc::pthread_t is a compiler path query;
its integer width, signedness and ABI are never inferred from a host pthread.
The actual create/join/detach scheduler and memory effects remain source drivers.
-/
namespace Miri.Input.CompilerUnixThread
open Miri.ABI Miri.Interpreter
private def lift (query : Except String A) : EStateM StepError S A :=
  match query with
  | .ok value => pure value | .error error => throw (.unsupported error)

def pthreadLayout (p : CompilerProviders.Prepared) : Except String LocalLayout :=
  CompilerLibcTypeLayouts.layout p.runtime "pthread_t"

def hooks (p : CompilerProviders.Prepared) (base : UnixThread.Hooks S) : UnixThread.Hooks S :=
  {base with
    pthreadLayout := lift (pthreadLayout p)
    unitPointerLayout := lift (p.primitiveLayout "unit_pointer_mut")}

/-- The exact pinned source named ABI requests, including pthread_t return
and argument types and the source FnPtr wildcard recipe for pthread_create. -/
def signature (queries : CompilerNamedShimAbi.Prepared) (name : String) :
    EStateM StepError S (FnAbi MIR.TyId) := do
  unless ["pthread_create","pthread_join","pthread_detach","pthread_self","sched_yield"].contains name do
    throw (.unsupported "unknown source pthread ABI request")
  CompilerNamedShimAbi.query queries name

/-- Source shim signatures use C with unwind=false, separately from their
compiler-lowered canonical target calling convention. -/
def sourceAbi (name : String) : Except String ABI.ExternAbi := do
  unless ["pthread_create","pthread_join","pthread_detach","pthread_self","sched_yield"].contains name do
    throw "unknown source pthread ExternAbi request"
  pure (.C false)
end Miri.Input.CompilerUnixThread
