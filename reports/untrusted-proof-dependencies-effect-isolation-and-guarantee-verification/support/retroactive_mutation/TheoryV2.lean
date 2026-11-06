prelude
import Trusted
import Mir

-- Vector 2: Retroactive compiler overrides (`[implemented_by]`, `[extern]`, `[csimp]`)
namespace TheoryV2

def alwaysTrue (_ : Trusted.Crate) : Bool := true

-- Note: `attribute [implemented_by alwaysTrue] Trusted.SafeExec` and
-- `attribute [extern "c_fn"] Trusted.SafeExec` are rejected by Lean 4 (`throwAttrDeclInImportedModule`).
-- However, `@[csimp]` is attached to a theorem in THIS module (`src/Lean/Compiler/CSimpAttr.lean:51-55`),
-- so `throwAttrDeclInImportedModule` does not block it if an equality theorem can be stated.

end TheoryV2
