/- Probe A3: can the KERNEL (not the native compiler) evaluate bv_decide's own verified
   LRAT checker `Std.Tactic.BVDecide.Reflect.verifyBVExpr` on the certificate that
   bv_decide produced?  If yes, `unsat_of_verifyBVExpr_eq_true` would give a
   trustLevel-0 proof with no `_native` axiom. -/
import Std.Tactic.BVDecide
import Lean
open Lean Elab Command

theorem a3_xor8 (x y : BitVec 8) : (x ^^^ y) ^^^ y = x := by bv_decide

-- list the aux constants bv_decide left in the environment
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.map₂.toList do
    if (`a3_xor8).isPrefixOf n then logInfo m!"{n}"

open Std.Tactic.BVDecide.Reflect in
#check @unsat_of_verifyBVExpr_eq_true
