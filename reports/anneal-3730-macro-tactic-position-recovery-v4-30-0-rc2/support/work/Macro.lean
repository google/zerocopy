syntax "solve_macro" term : tactic
macro_rules | `(tactic| solve_macro $t) => `(tactic| exact $t)
theorem q (h : True) : True := by
  solve_macro ?_
