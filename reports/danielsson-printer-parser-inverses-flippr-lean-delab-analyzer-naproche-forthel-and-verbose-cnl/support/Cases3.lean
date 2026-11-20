import Lean
set_option autoImplicit false
universe u u_1
set_option pp.numericTypes true
-- default-printed text of Lean.Grind.AddCommGroup.neg_zero, re-elaborated
#check ∀ {M : Type u} [inst : Lean.Grind.AddCommGroup M], -0 = 0
-- pp.analyze-printed text of Array.prod_empty, re-elaborated
#check ∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α], Array.prod #[] = 1
-- default-printed text of BitVec.toNat_mod_cancel', re-elaborated, vs original
#check ∀ {n : Nat} {x : BitVec n}, ↑x.toNat % ↑(2 ^ n) = ↑x.toNat
set_option pp.coercions.types true in
#check @BitVec.toNat_mod_cancel'
