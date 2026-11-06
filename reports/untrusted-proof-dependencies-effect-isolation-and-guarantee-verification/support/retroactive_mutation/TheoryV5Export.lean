prelude
import Trusted
import Mir

-- Vector 5c: `export` alias shadowing
-- Notice: `Parser.Command.export` is in `TrustedBoundary.allowedCommandKinds`!
abbrev CrateAlias2 := Trusted.Crate

namespace FakeShadow
namespace Trusted

def CrateTheorem (_ : CrateAlias2) : Prop :=
  True

end Trusted
end FakeShadow

export FakeShadow (Trusted.CrateTheorem)
