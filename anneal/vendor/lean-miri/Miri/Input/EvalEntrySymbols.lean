import Miri.Input.EvalWorld
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Interpreter.ExecutionStateTransport

/-! Outer bootstrap view of the same source intrinsic registry used by the
inner execution core. Reassociation changes no allocation/type identity. -/
namespace Miri.Input.EvalEntrySymbols
open Miri.Memory Miri.Interpreter
abbrev W := EvalWorld.World

def access : IntrinsicSymbolsMachine.Access (EvalWorld.User Os R P H D O Aff B Host) where
  get := fun user => user.user.payload.payload.symbols
  put := fun user symbols => {user with user := {user.user with payload :=
    {user.user.payload with payload := {user.user.payload.payload with symbols}}}}

theorem get_put (user : EvalWorld.User Os R P H D O Aff B Host) (registry : IntrinsicSymbolsMachine.Registry) :
    access.get (access.put user registry) = registry := rfl

theorem put_get (user : EvalWorld.User Os R P H D O Aff B Host) :
    access.put user (access.get user) = user := rfl

def attach (p : CompilerProviders.Prepared) (image : AllocationImage.Imported) :
    MachineHooks.M MiriMemoryKind (EvalWorld.User Os R P H D O Aff B Host) Unit :=
  CompilerIntrinsicSymbols.attach p image access
end Miri.Input.EvalEntrySymbols
