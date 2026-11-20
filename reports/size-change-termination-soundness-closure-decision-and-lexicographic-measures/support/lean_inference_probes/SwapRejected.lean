-- Lean termination-inference probe (core Lean only). Expected with Lean v4.34.1: an error
-- "Could not find a decreasing measure." for the permuting call.
def swapF (x y : Nat) : Nat := if x = 0 then 0 else swapF y (x - 1)
