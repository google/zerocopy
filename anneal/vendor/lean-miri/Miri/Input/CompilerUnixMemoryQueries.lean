import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerLibcConstants
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.UnixMemory
import Miri.Interpreter.IoError
import Miri.Interpreter.ScalarOps

/-! Bind actual compiler libc value/signature evidence into the existing
physical Unix memory and errno pipelines. Missing names remain unsupported;
page-size, host errors, memory accesses and frame checks are runtime effects.
-/
namespace Miri.Input.CompilerUnixMemoryQueries
open Miri.ABI Miri.Memory Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler libc query: {reason}")

def ioErrorHooks (constants : CompilerNamedConstants.Prepared) (base : IoError.Hooks S Host) :
    IoError.Hooks S Host :=
  { base with libc := fun name => lift (CompilerLibcConstants.scalar constants name) }

def hooks (constants : CompilerNamedConstants.Prepared) (abis : CompilerNamedShimAbi.Prepared)
    (base : UnixMemory.Hooks P S D MD B I) : UnixMemory.Hooks P S D MD B I :=
  { base with
    expectedAbi := CompilerNamedShimAbi.query abis
    libcI32 := fun name => lift (CompilerLibcConstants.i32 constants name)
    mapFailed := lift (CompilerLibcConstants.scalar constants "MAP_FAILED") }

/-- mmap offset conversion uses actual compiler libc::off_t size, independent
of host width and pointer width. readScalar must be the real operand read. -/
def readOffset [PointerProvenance P] (runtime : RuntimeMetadata)
    (readScalar : OpTy P → EStateM StepError S (Scalar P)) (operand : OpTy P) :
    EStateM StepError S Int := do
  let scalar ← readScalar operand
  let layout ← lift (CompilerPrimitiveFacts.offTLayout runtime)
  match scalar.toInt layout.layout.size with
  | .ok value => pure value
  | .error error => throw (ScalarOps.scalarError error)
end Miri.Input.CompilerUnixMemoryQueries
