import Miri.Input.CompilerUnixThread
import Miri.Input.CompilerProviders
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerLibcConstants
import Miri.Interpreter.LinuxSyscall

/-! Actual linux_like/{syscall,sync,thread,eventfd}.rs compiler requests.
Types come from exact constructor/path keys, and constants from target rustc
const_eval_instance. No host libc/triple table or layout-equality type lookup.
-/
namespace Miri.Input.CompilerLinuxSyscall
open Miri.ABI Miri.Memory Miri.Interpreter
private def lift (query : Except String A) : EStateM StepError S A :=
  match query with
  | .ok value => pure value | .error error => throw (.unsupported error)

/-- Ordered source shim_varargs type requests; pointer pointees retain exact
canonical compiler identity even when their layouts happen to coincide. -/
def argumentLayout (p : CompilerProviders.Prepared) : LinuxFutex.ArgType → Except String LocalLayout
  | .u32Pointer => CompilerPrimitiveFacts.namedLayout p.runtime "u32_pointer"
  | .timespecPointer => CompilerPrimitiveFacts.namedLayout p.runtime "libc_timespec_pointer"
  | .i32 => p.primitiveLayout "i32"
  | .u32 => p.primitiveLayout "u32"
  | .voidPointer => CompilerPrimitiveFacts.namedLayout p.runtime "libc_c_void_pointer"
  | .usize => p.primitiveLayout "usize"
  | .charPointer => CompilerPrimitiveFacts.namedLayout p.runtime "libc_c_char_pointer"
  | .sockaddrPointer => CompilerPrimitiveFacts.namedLayout p.runtime "libc_sockaddr_pointer"
  | .socklenPointer => CompilerPrimitiveFacts.namedLayout p.runtime "libc_socklen_t_pointer"

def argumentTypes (p : CompilerProviders.Prepared) (types : Array LinuxFutex.ArgType) :
    Except String (Array MIR.TyId) :=
  types.mapM fun type => return (← argumentLayout p type).ty

def timespecLayout (runtime : RuntimeMetadata) : Except String LocalLayout :=
  CompilerPrimitiveFacts.namedLayout runtime "libc_timespec"

/-- Source `eval_libc(...).to_target_usize`: actual target pointer-sized scalar
conversion, including overflow/provenance failures rather than host casts. -/
def libcUsize (constants : CompilerNamedConstants.Prepared) (name : String) :
    EStateM StepError S UInt64 := do
  let scalar : Scalar Provenance ← lift (CompilerLibcConstants.scalar constants name)
  match scalar.toTargetUsize constants.runtime.target.pointerSize with
  | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)

def signature (queries : CompilerNamedShimAbi.Prepared) (name : String) :
    EStateM StepError S (FnAbi MIR.TyId) := do
  unless name == "syscall" || name == "prctl" do throw (.unsupported "unknown source Linux syscall ABI request")
  CompilerNamedShimAbi.query queries name

def sourceAbi (name : String) : Except String ABI.ExternAbi := do
  unless name == "syscall" || name == "prctl" do throw "unknown source Linux syscall ExternAbi request"
  pure (.C false)

def futexHooks (constants : CompilerNamedConstants.Prepared) (base : LinuxFutex.Hooks S R) :
    LinuxFutex.Hooks S R :=
  {base with libcI32 := fun name => lift (CompilerLibcConstants.i32 constants name)}

def eventHooks (p : CompilerProviders.Prepared) (constants : CompilerNamedConstants.Prepared)
    (base : EventFd.Hooks S F) : EventFd.Hooks S F :=
  {base with
    libcI32 := fun name => lift (CompilerLibcConstants.i32 constants name)
    u64Layout := lift (p.primitiveLayout "u64")}

/-- Actual memory, time, isolation, synchronization, fd and thread actions stay
in the canonical runtime hooks. The varargs checker consumes these exact TyIds.
-/
def hooks (p : CompilerProviders.Prepared) (constants : CompilerNamedConstants.Prepared)
    (abis : CompilerNamedShimAbi.Prepared) (base : LinuxSyscall.Hooks S R F D B I) :
    LinuxSyscall.Hooks S R F D B I :=
  {base with
    signature := signature abis
    argumentTypes := fun types => lift (argumentTypes p types)
    libcUsize := libcUsize constants
    libcI32 := fun name => lift (CompilerLibcConstants.i32 constants name)
    futex := futexHooks constants base.futex
    event := eventHooks p constants base.event
    thread := CompilerUnixThread.hooks p base.thread}
end Miri.Input.CompilerLinuxSyscall
