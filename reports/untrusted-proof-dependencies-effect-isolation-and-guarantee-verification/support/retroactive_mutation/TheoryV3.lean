prelude
import Trusted
import Mir

-- Vector 3: High-priority (or LIFO default-priority) typeclass instance overriding
namespace TheoryV3

-- Even WITHOUT `(priority := 1000000)` (which Phase 1 blocks via `inspectNodeKind`),
-- a default-priority `instance` in `TheoryV3` takes precedence over older instances in `Init`
-- via Lean's LIFO typeclass synthesis order!
-- Here we define a `Coe` or `OfNat` instance.
instance (priority := 1000000) : OfNat Nat n where
  ofNat := 1

instance (priority := 1000000) : BEq Nat where
  beq _ _ := true

end TheoryV3
