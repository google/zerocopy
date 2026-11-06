prelude
import Trusted
import Mir

-- Vector 1: Retroactive attributes (`[simp]`, `[reducible]`, `[irreducible]`) on `Trusted.*`
-- 1a. `attribute [simp] Trusted.SafeExec` is allowed across modules in Lean 4 AND allowed by Phase 1.
attribute [simp] Trusted.SafeExec

-- 1b. Without `allowUnsafeReducibility`, `attribute [reducible] Trusted.SafeExec` fails on imported decls.
-- With `set_option allowUnsafeReducibility true`, Lean 4 allows global retroactive reducibility
-- changes via `reducibilityExtraExt` (`src/Lean/ReducibilityAttrs.lean:71-77, 95`)!
set_option allowUnsafeReducibility true in
attribute [irreducible] Trusted.SafeExec
