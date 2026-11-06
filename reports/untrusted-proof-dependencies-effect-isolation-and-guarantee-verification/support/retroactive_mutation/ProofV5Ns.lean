prelude
import Trusted
import Mir
import TheoryV5Ns

namespace Proof

-- In ProofV5Ns, the source text literally says `theorem verify_crate : Trusted.CrateTheorem Mir.crate`
-- inside `namespace Proof`. Because `TheoryV5Ns` declared `Proof.Trusted.CrateTheorem`, Lean's
-- name resolution inside `namespace Proof` resolves `Trusted.CrateTheorem` to
-- `Proof.Trusted.CrateTheorem` (`True`) instead of `_root_.Trusted.CrateTheorem`!
theorem verify_crate : Trusted.CrateTheorem Mir.crate :=
  trivial

end Proof
