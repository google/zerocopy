import Lean
syntax "probe_tac" : tactic
macro_rules | `(tactic| probe_tac) => `(tactic| skip)
def selected : Nat := 9
