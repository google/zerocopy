import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerNamedShimAbi
import Miri.Interpreter.CpuAffinityDispatch

/-! Canonical compiler c_ulong layout and pid_t signature evidence for the
source CPU affinity machine. Missing queries remain unresolved execution. -/
namespace Miri.Input.CompilerCpuAffinity
open Miri.Interpreter

def hooks (runtime : RuntimeMetadata)
    (base : CpuAffinity.Hooks P S MD) : CpuAffinity.Hooks P S MD :=
  {base with chunkSize := do
    let layout ← match CompilerPrimitiveFacts.cULongLayout runtime with
      | .ok layout => pure layout
      | .error reason => throw (.unsupported reason)
    return layout.layout.size.bytes.toNat}

def dispatch (runtime : RuntimeMetadata) (queries : CompilerNamedShimAbi.Prepared)
    (base : CpuAffinityDispatch.Hooks P S D MD B I) : CpuAffinityDispatch.Hooks P S D MD B I :=
  {base with
    affinity := hooks runtime base.affinity
    expectedAbi := CompilerNamedShimAbi.query queries}
end Miri.Input.CompilerCpuAffinity
