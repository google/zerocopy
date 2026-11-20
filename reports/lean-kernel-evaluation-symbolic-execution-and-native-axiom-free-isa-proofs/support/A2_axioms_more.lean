/- Probe A2: more axiom footprints (Lean v4.34.1): bv_decide closed by normalization,
   grind (incl. ring / linarith modules), decide +kernel, simp-arith. -/
import Std.Tactic.BVDecide

-- (1) bv_decide on a goal that bv_normalize alone already closes: is an aux axiom emitted?
theorem a2_bvdecide_trivial (x : BitVec 64) : x + 0 = x := by bv_decide
#print axioms a2_bvdecide_trivial

-- (2) grind on a BitVec / Nat goal
theorem a2_grind_nat (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c := by grind
#print axioms a2_grind_nat

-- (3) grind ring module on commutative ring identity over Int
theorem a2_grind_ring (a b : Int) : (a + b) * (a - b) = a * a - b * b := by grind
#print axioms a2_grind_ring

-- (4) grind ring over BitVec 64 (BitVec 64 is a commutative ring)
theorem a2_grind_ring_bv (a b : BitVec 64) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by grind
#print axioms a2_grind_ring_bv

-- (5) grind linarith over Int
theorem a2_grind_lin (a b : Int) (h : 2 * a + 3 * b ≤ 5) (h2 : 0 ≤ b) : 2 * a ≤ 5 := by grind
#print axioms a2_grind_lin

-- (6) decide +kernel on a finite enumeration (BitVec 8, all 256 values)
theorem a2_decide_kernel_bv8 : ∀ x : BitVec 8, x ^^^ x = 0 := by decide +kernel
#print axioms a2_decide_kernel_bv8

-- (7) simp +arith
theorem a2_simp_arith (a : Nat) : a + 2 + 3 = 5 + a := by simp +arith
#print axioms a2_simp_arith

-- (8) BitVec.toNat + omega style
theorem a2_toNat_omega (x : BitVec 64) (h : x.toNat < 2^32) : (x + x).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_add]; omega
#print axioms a2_toNat_omega
