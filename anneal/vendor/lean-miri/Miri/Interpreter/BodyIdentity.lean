import Miri.MIR.Syntax

/-! Identity of an actual compiler MIR body in the fixed program's body table.
This is independent of structural body equality, diagnostic names or spans. -/
namespace Miri.Interpreter

structure BodyIdentity where
  private mk ::
  index : Nat
  deriving DecidableEq, Repr

namespace BodyIdentity
/-- Called by the program loader with its exact compilation-local body key. -/
def ofCanonicalIndex (index : Nat) : BodyIdentity := ⟨index⟩
end BodyIdentity

structure LoadedBody where
  identity : BodyIdentity
  body : MIR.Body
  deriving DecidableEq, Repr

end Miri.Interpreter
