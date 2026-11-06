prelude
import Trusted
import Mir

-- Vector 5b: Namespace shadowing (`Proof.Trusted.CrateTheorem`)
-- Notice:
-- 1. Every syntax node in this file is in `TrustedBoundary.allowedTheorySyntaxKinds`!
-- 2. Every identifier passes `TrustedBoundary.isValidSourceIdent` (no `_root_`)!
-- 3. The declared constant is `Proof.Trusted.CrateTheorem`, whose `.getRoot` is `Proof` (NOT `Trusted`),
--    so `TrustedBoundary.validateLocalConstant` (`(privateToUserName ci.name).getRoot == `Trusted`)
--    does NOT reject it!
abbrev CrateAlias := Trusted.Crate

namespace Proof.Trusted

def CrateTheorem (_ : CrateAlias) : Prop :=
  True

end Proof.Trusted
