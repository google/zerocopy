/- Probe: which axiom does native evaluation contribute to a `bv_decide` / `native_decide`
   proof? Run unchanged under Lean v4.29.0, v4.34.1 and v4.35.0. Imports only Std's BVDecide. -/
import Std.Tactic.BVDecide
-- reaches the SAT/LRAT stage
theorem a6_bv (x y : BitVec 64) : (x ^^^ y) ^^^ y = x := by bv_decide
#print axioms a6_bv
-- closed by bv_decide's normalization front end alone (no SAT call)
theorem a6_bv_trivial (x : BitVec 64) : x + 0 = x := by bv_decide
#print axioms a6_bv_trivial
-- native_decide for contrast
theorem a6_nd : (0x123456789#64) * 0x1000#64 = 0x123456789000#64 := by native_decide
#print axioms a6_nd
