import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Interpreter.UnixTlsDispatch

/-! Exact common Unix pthread-key and atfork signature/type queries. Source
function-pointer wildcards are compiler shim recipes, never guessed C ABIs. -/
namespace Miri.Input.CompilerUnixTls
open Miri.ABI Miri.Interpreter

def signature (prepared : CompilerNamedShimAbi.Prepared) (name : String) :
    EStateM StepError S (FnAbi MIR.TyId) := do
  unless #["pthread_key_create","pthread_key_delete","pthread_getspecific",
      "pthread_setspecific","pthread_atfork"].contains name do
    throw (.unsupported "unknown source pthread TLS signature request")
  CompilerNamedShimAbi.query prepared name

def keyLayout (runtime : RuntimeMetadata) : EStateM StepError S LocalLayout :=
  match CompilerLibcTypeLayouts.layout runtime "pthread_key_t" with
  | .ok layout => pure layout
  | .error error => throw (.unsupported error)

def hooks (runtime : RuntimeMetadata) (prepared : CompilerNamedShimAbi.Prepared)
    (base : UnixTlsDispatch.Hooks S D B I) : UnixTlsDispatch.Hooks S D B I :=
  {base with signature := signature prepared, keyLayout := keyLayout runtime}
end Miri.Input.CompilerUnixTls
