import Dep
syntax "solve_macro" term : tactic
macro_rules | `(tactic| solve_macro $t) => `(tactic| exact $t)
theorem positioned (h : depValue = 7) : depValue = 7 := by
  solve_macro h
