import Lean
open Lean Elab Tactic
elab "pause" : tactic => do
  IO.sleep 3000
  evalTactic (← `(tactic| trivial))
theorem slow : True := by
  pause
