import Lean
syntax "new_tac" : tactic
macro_rules | `(tactic| new_tac) => `(tactic| decide)
