import Lean
open Lean Elab Tactic
elab "pause" : tactic => do
  IO.sleep 1500
  evalTactic (← `(tactic| trivial))
theorem target : True := by
  trace_state
  pause
#print axioms target
