prelude
import Trusted
import Mir
import TheoryV5Export

-- Even OUTSIDE `namespace Proof`, if `Proof.lean` opens `Trusted` (or `FakeShadow`)
-- and writes `CrateTheorem Mir.crate`, or if `export` shadows an unqualified name:
open Trusted

theorem verify_unqualified : CrateTheorem Mir.crate :=
  -- Wait: let's see how Lean resolves `Trusted.CrateTheorem` vs `CrateTheorem` when `export` is present!
  rfl
