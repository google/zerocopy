module

public import Dep

-- (a) When Consumer writes `public import Dep` (WITHOUT `meta import Dep`):
--     1. Dep's `meta initialize` STILL runs at import time!
--     2. Dep's non-meta `initialize` does NOT run!
--     3. Dep's public syntax, macros, custom command elaborators, custom tactics,
--        and `@[simp]` lemmas ALL work in Consumer!
public def testMacro : Nat := dep_macro_val
#dep_cmd
public theorem testTac : depPublicVal = 100 := by dep_tac
public theorem testSimp : depUnexposedVal = 77 := by simp

-- (b) Verify that `depPrivateHelper` is hidden under `public import Dep`:
/-- error: Unknown identifier `depPrivateHelper` -/
#guard_msgs in
#check depPrivateHelper

-- (c) Verify that `depUnexposedVal` cannot be unfolded by `rfl` because its body is erased
--     to `axiomInfo` in `Dep.olean`:
/--
error: Tactic `rfl` failed: The left-hand side
  depUnexposedVal
is not definitionally equal to the right-hand side
  77

⊢ depUnexposedVal = 77
-/
#guard_msgs in
theorem testUnexposed : depUnexposedVal = 77 := by rfl

-- (d) Verify that calling non-meta `depPublicVal` inside a `meta def` / `@[term_elab]` fails
--     when `Dep` is NOT `meta import`ed:
syntax (name := callNonMeta) "call_nonmeta" : term

/--
error: Invalid `meta` definition `elabCallNonMeta`, `depPublicVal` is not accessible here; consider adding `public meta import Dep`
-/
#guard_msgs in
@[term_elab callNonMeta]
public meta def elabCallNonMeta : Lean.Elab.Term.TermElab := fun _ _ => do
  let n := depPublicVal
  return Lean.mkNatLit n
