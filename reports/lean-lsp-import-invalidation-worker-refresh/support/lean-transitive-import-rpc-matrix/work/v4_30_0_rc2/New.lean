import Mid
open Lean Elab Command
run_cmd do logInfo s!"OPTION={(← getOptions).getBool `pp.universes false}"
#eval transitive
theorem data : transitive = 7 := by rfl
theorem macro_check : True := by probe_tac
theorem rpc_check (n : Nat) (h : n = transitive) : n = transitive := by
  exact ?_
