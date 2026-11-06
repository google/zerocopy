module

public import Lean

public section

-- 1. Runtime (non-meta) initialize: stored in Dep.ir (not Dep.olean), IRPhases.runtime
initialize
  IO.println "[Dep:runtime-init] non-meta `initialize` executed!"

-- 2. Meta initialize: stored in Dep.olean, IRPhases.comptime
meta initialize
  IO.println "[Dep:meta-init] `meta initialize` executed!"

-- 3. Public exposed def, public unexposed def, private def, and public theorem
@[expose] def depPublicVal : Nat := 100
def depUnexposedVal : Nat := 77
private def depPrivateHelper : Nat := 42
theorem depPublicThm : depPublicVal = 100 := by rfl

-- 4. Public syntax + macro exported from a `module`
syntax (name := depMacro) "dep_macro_val" : term
macro_rules
  | `(dep_macro_val) => `(12345)

-- 5. Public custom command elaborator exported from a `module`
syntax (name := depCmd) "#dep_cmd" : command
@[command_elab depCmd]
meta def elabDepCmd : Lean.Elab.Command.CommandElab := fun _ => do
  IO.println "[Dep:elabDepCmd] custom command elaborator from Dep executed!"

-- 6. Public custom tactic exported from a `module`
syntax (name := depTac) "dep_tac" : tactic
@[tactic depTac]
meta def evalDepTac : Lean.Elab.Tactic.Tactic := fun _ => do
  IO.println "[Dep:evalDepTac] custom tactic from Dep executed!"
  Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

-- 7. Public @[simp] attribute on a theorem in Dep
@[simp] theorem depSimpLemma : depUnexposedVal = 77 := by rfl

end
