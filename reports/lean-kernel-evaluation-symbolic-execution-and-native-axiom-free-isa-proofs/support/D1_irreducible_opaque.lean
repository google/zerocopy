/- Probe D1: what do reducibility attributes / opaque wrappers do to kernel evaluation? -/
@[irreducible] def fIrr (n : Nat) : Nat := n + 1
opaque gOpq : Nat → Nat := fun n => n + 1
def hPlain (n : Nat) : Nat := n + 1

-- kernel ignores @[irreducible]:
theorem d1_irr_kernel : fIrr 3 = 4 := by decide +kernel
#print axioms d1_irr_kernel
-- elaborator respects @[irreducible]:
theorem d1_irr_elab : fIrr 3 = 4 := by decide
-- opaque constants are never unfolded, not even by the kernel:
theorem d1_opaque_kernel : gOpq 3 = 4 := by decide +kernel
-- plain def:
theorem d1_plain : hPlain 3 = 4 := by decide
#print axioms d1_plain
