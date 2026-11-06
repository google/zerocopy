prelude
import Trusted
import Mir
import TheoryV3

namespace Proof

-- Case 3A: When the theorem statement is pure constant application `Trusted.CrateTheorem Mir.crate`,
-- `Trusted.SafeExec` and `Mir.crate` were ALREADY elaborated when `Trusted.lean` and `Mir.lean` were
-- compiled (before `TheoryV3` was imported), so `TheoryV3`'s `OfNat`/`BEq` instances cannot alter
-- `Trusted.CrateTheorem Mir.crate`.
-- However, if a theorem statement in `Proof.lean` elaborates any typeclass-mediated syntax
-- (such as `0 == 1` or `Mir.crate.entryReturnVal == 1` using `==` / literals), `TheoryV3`'s
-- instances hijack the elaborated statement in `Proof.lean`!
theorem verify_typeclass_stmt : (Mir.crate.entryReturnVal == Mir.crate.expectedVal) = true :=
  rfl

end Proof
