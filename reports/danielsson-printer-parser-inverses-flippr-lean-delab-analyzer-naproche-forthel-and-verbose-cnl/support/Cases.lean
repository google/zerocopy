import Lean
open Lean Elab Term Meta Command

set_option autoImplicit false

-- Case 1: `∃ h, ...` whose binder type is printed nowhere
#check @Array.mapFinIdx_eq_iff
set_option pp.funBinderTypes true in
#check @Array.mapFinIdx_eq_iff

-- Case 2: scoped notation printed outside its scope
#check @BitVec.ofNatLT_zero
#check ∀ {w : Nat} {h : 0 < 2 ^ w}, BitVec.ofNatLT 0 h = 0#w

-- Case 3: unapplied polymorphic operators
#check @Array.foldl_min
example : True := by
  have := (inferInstance : Inhabited Nat)
  trivial
