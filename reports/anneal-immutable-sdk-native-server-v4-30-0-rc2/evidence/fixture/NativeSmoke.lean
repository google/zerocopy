import AeneasMeta.Saturate.Tactic
import Mathlib.Data.Nat.Basic

#check Nat.succ_injective

example : True := by
  aeneas_saturate

  trivial
