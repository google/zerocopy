prelude
import Trusted
import Mir
import TheoryV4

namespace Proof

-- In ProofV4, the source text literally says `theorem verify_crate : Trusted.CrateTheorem Mir.crate`,
-- but `TheoryV4`'s notation rewrites `Trusted.CrateTheorem Mir.crate` to `True` during elaboration!
theorem verify_crate : Trusted.CrateTheorem Mir.crate :=
  rfl

end Proof
