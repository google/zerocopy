import Lean
syntax "probe_decide" : tactic
macro_rules | `(tactic| probe_decide) => `(tactic| decide)
