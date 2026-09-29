import Lean
syntax "probe_tac" : tactic
macro_rules | `(tactic| probe_tac) => `(tactic| decide)
def selected : Nat := 7
