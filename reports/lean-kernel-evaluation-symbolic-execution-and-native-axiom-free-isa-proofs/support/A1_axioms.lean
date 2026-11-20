/- Probe A1: axiom footprint of bv_decide and friends on 64-bit identities (Lean v4.34.1). -/
import Std.Tactic.BVDecide

-- (1) plain bv_decide on a 64-bit identity
theorem a1_bvdecide_xor (x y : BitVec 64) : (x ^^^ y) ^^^ y = x := by bv_decide
#print axioms a1_bvdecide_xor

-- (2) bv_decide on a 64-bit mul identity (needs bitblasting of mul)
theorem a1_bvdecide_mul (x : BitVec 64) : x * 3 = x + x + x := by bv_decide
#print axioms a1_bvdecide_mul

-- (3) bv_normalize alone (rewriting front end, no SAT call)
theorem a1_bvnormalize (x : BitVec 64) : x + 0 = x := by bv_normalize
#print axioms a1_bvnormalize

-- (4) bv_omega
theorem a1_bvomega (x : BitVec 64) (h : x < 10) : x + 1 ≤ 10 := by bv_omega
#print axioms a1_bvomega

-- (5) omega over Nat
theorem a1_omega (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
#print axioms a1_omega

-- (6) simp with BitVec simprocs on literals
theorem a1_simp_lit : (0xFFFFFFFFFFFFFFFF#64) + 1#64 = 0#64 := by simp
#print axioms a1_simp_lit

-- (7) decide (elaborator + kernel) and decide +kernel on closed BitVec 64 terms
theorem a1_decide : (0x123456789#64) * 0x1000#64 = 0x123456789000#64 := by decide
#print axioms a1_decide
theorem a1_decide_kernel : (0x123456789#64) * 0x1000#64 = 0x123456789000#64 := by decide +kernel
#print axioms a1_decide_kernel

-- (8) rfl on closed BitVec 64 terms (kernel Nat GMP acceleration)
theorem a1_rfl : (0xdeadbeef#64).sdiv (-3#64) = 0xffffffffb5c615b1#64 := by rfl
#print axioms a1_rfl

-- (9) native_decide (forbidden in Anneal) for contrast
theorem a1_native : (0x123456789#64) * 0x1000#64 = 0x123456789000#64 := by native_decide
#print axioms a1_native
