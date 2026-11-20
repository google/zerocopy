/-! Identity of a frame's locals backing buffer (stack.rs locals_addr).
This is interpreter metadata, not a Rust allocation or pointer provenance. -/
namespace Miri.Interpreter

structure LocalsIdentity where
  private mk ::
  token : Nat
  deriving DecidableEq, Repr

namespace LocalsIdentity
/-- The embedding supplies the actual abstract host-buffer token. Equal tokens
represent equal buffer identity; a host allocator may explicitly reuse tokens. -/
def ofAllocationToken (token : Nat) : LocalsIdentity := ⟨token⟩
end LocalsIdentity

/-- Optional lifetime-unique ghost labeling discipline. Callers supply a next
unused token explicitly; no frame receives an invented default identity. This
labels lifetimes rather than modeling possible host-address reuse. -/
structure LocalsIdentitySupply where
  nextUnused : Nat
  deriving Repr

def LocalsIdentitySupply.allocate (supply : LocalsIdentitySupply) :
    LocalsIdentitySupply × LocalsIdentity :=
  (⟨supply.nextUnused + 1⟩, .ofAllocationToken supply.nextUnused)

end Miri.Interpreter
