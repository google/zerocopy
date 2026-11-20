/- Probe A6: which axiom does native evaluation use, per toolchain? (run with v4.29.0, v4.34.1, v4.35.0) -/
import Std.Tactic.BVDecide
theorem a6_bv (x y : BitVec 64) : (x ^^^ y) ^^^ y = x := by bv_decide
#print axioms a6_bv
theorem a6_nd : (0x123456789#64) * 0x1000#64 = 0x123456789000#64 := by native_decide
#print axioms a6_nd
