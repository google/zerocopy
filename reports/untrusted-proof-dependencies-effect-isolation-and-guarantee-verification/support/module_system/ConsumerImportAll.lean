module

public import Dep
import all Dep

-- With `import all Dep`:
-- 1. Private definitions (`depPrivateHelper`) from `Dep.olean.private` are visible in private scope:
theorem exposePrivate : depPrivateHelper = 42 := by rfl

-- 2. Unexposed public definitions (`depUnexposedVal`) have their `.defnInfo` body restored from
--    `Dep.olean.private` and can now be unfolded by `rfl`:
theorem exposeUnexposed : depUnexposedVal = 77 := by rfl
