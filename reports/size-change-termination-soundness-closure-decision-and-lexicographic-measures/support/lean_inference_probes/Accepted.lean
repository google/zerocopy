-- Lean termination-inference probes (core Lean only). Expected with Lean v4.34.1: no errors, and
-- the inferred measures `(x1, x2)` for `ack` and `100 - x` for `countUp` are printed.
set_option showInferredTerminationBy true

def swapF2 (x y : Nat) : Nat := if x = 0 then 0 else swapF2 y (x - 1)
termination_by x + y

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

def countUp (x : Nat) : Nat := if x < 100 then countUp (x + 1) else 0
