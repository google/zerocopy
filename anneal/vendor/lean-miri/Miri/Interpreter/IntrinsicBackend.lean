import Miri.Interpreter.Intrinsics

namespace Miri.Interpreter.IntrinsicBackend
open Miri.Memory Miri.MIR
inductive Kind where
  | none | vclocks
structure Dispatcher (S C V : Type) where
  selection : S → Except StepError Kind

def eval (backend : Dispatcher S C V) (hooks : IntrinsicHooks Provenance S C V)
    (choice : C) (name : String) (types : Array TyId) (args : Array (OpTy Provenance))
    (dest : V) (ret : Option BasicBlockId) : RvalueM S Bool := do
  if name.startsWith "atomic_" then
    let _ ← match backend.selection (← get) with
      | .ok selected => pure selected | .error error => throw error
    IntrinsicAtomic.eval hooks.atomicHooks choice name args dest ret
  else Intrinsics.eval hooks choice name types args dest ret
end Miri.Interpreter.IntrinsicBackend
