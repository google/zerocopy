import Lean.Elab.Tactic.Omega

-- A commuted nonlinear product is not the same syntactic atom in this probe.
example (a b : Nat) : a * b = b * a := by omega
