prelude
import Trusted

namespace Mir

-- A buggy crate: entryReturnVal (0) != expectedVal (1).
-- Under the genuine `Trusted.CrateTheorem`, `Trusted.CrateTheorem Mir.crate`
-- is `Nat.beq 0 1 = true` (`false = true`), which is unprovable in a consistent kernel.
def crate : Trusted.Crate :=
  { entryReturnVal := 0, expectedVal := 1 }

end Mir
