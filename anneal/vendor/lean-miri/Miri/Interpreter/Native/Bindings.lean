import Miri.Interpreter.Native.Runtime
import Miri.Interpreter.Call

namespace Miri.Interpreter.Native
open Miri.ABI Miri.Memory Miri.MIR
/-- Install the concrete Rust supervisor/interchange pipeline around the only
remaining actual libffi invocation leaf. The external implementation must build
the source Cif from descriptors, consume each descriptor exactly once, and
allocate the return buffer of the supplied byte size before invoking the code. -/
def withSupervisor (h : Hooks P S C V Code) (child : Trace.ChildHooks S C)
    (ffi : C → Code → Array OwnedArg → FfiType → Size → RvalueM S (Array UInt8)) : Hooks P S C V Code :=
  { h with rawCall := fun choice code args ret size =>
      Trace.rawCall child choice (ffi choice code args ret size) }

/-- Canonical call operands retain InPlace arguments as their original memory
places. This matches source copy_fn_args; moving/resetting them is not invented. -/
def callFnArgs [PointerProvenance P] (h : Hooks P S C V Code) (choice : C)
    (fuel : Nat) (name : String) (dest : V) (args : Array (FnArg P)) : RvalueM S Bool :=
  call h choice fuel name dest (args.map FnArg.copyFnArg)
end Miri.Interpreter.Native
