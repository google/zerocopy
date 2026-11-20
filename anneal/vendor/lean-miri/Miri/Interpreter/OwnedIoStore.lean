import Miri.Interpreter.OwnedIoRuntime
import Miri.Interpreter.OwnedVirtualSocket
import Miri.Interpreter.OwnedTcpSocket

/-! One positive source callback sum for all owned IO families. Old source IO
adapters use a filtered value view, whose setter preserves every other family
from the current canonical store. No shadow store or counter is allocated.
Callback lookup/take is by unique token; array order is not observed. -/
namespace Miri.Interpreter.OwnedIoStore
inductive Capture (F : Type) where
  | io (value : OwnedIoRuntime.Capture F)
  | virtual (value : OwnedVirtualSocket.Capture F)
  | tcp (value : OwnedTcpSocket.Capture F)
  | owner (fd : F)
structure Storage (F : Type) where
  callbacks : Array (Nat × Capture F) := #[]
def base (s : Storage F) : OwnedIoRuntime.Storage F :=
  ⟨s.callbacks.filterMap fun (token,value) => match value with
    | .io value => some (token,value) | _ => none⟩
def putBase (s : Storage F) (value : OwnedIoRuntime.Storage F) : Storage F :=
  ⟨(s.callbacks.filter fun (_,value) => match value with | .io _ => false | _ => true) ++
    value.callbacks.map (fun (token,value) => (token,.io value))⟩
end Miri.Interpreter.OwnedIoStore
