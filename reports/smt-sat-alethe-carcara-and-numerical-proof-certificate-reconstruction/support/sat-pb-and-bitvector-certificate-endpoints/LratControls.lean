import Lean
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser
open Std.Sat Std.Tactic.BVDecide

def sourceCnf : CNF Nat := ⟨#[[(1, true)], [(1, false)]]⟩
def changedCnf : CNF Nat := ⟨#[[(1, true)], [(2, false)]]⟩
def goodCertificate : Array LRAT.IntAction := #[.addEmpty 3 #[1, 2]]
def shorterCertificate : Array LRAT.IntAction := #[.addEmpty 3 #[1]]

theorem goodAccepted : LRAT.check goodCertificate sourceCnf = true := by native_decide
theorem shorterAccepted : LRAT.check shorterCertificate sourceCnf = true := by native_decide
theorem changedRejected : LRAT.check goodCertificate changedCnf = false := by native_decide
theorem changedSatWitness : changedCnf.Sat (fun n => n == 1) := by
  unfold CNF.Sat
  decide +kernel

theorem sourceUnsat : sourceCnf.Unsat := LRAT.check_sound goodCertificate sourceCnf (by native_decide)

#eval LRAT.check goodCertificate sourceCnf
#eval LRAT.check shorterCertificate sourceCnf
#eval LRAT.check goodCertificate changedCnf
#eval LRAT.parseLRATProof "3 0 1 2 0\n".toUTF8
#print axioms goodAccepted
#print axioms shorterAccepted
#print axioms changedRejected
#print axioms changedSatWitness
#print axioms sourceUnsat
