import Std
namespace Inline
abbrev Byte := Fin 256
inductive Outcome where | ok (value : Nat) | panic | ub | div deriving DecidableEq
 def callee (x : Byte) : Outcome := if x.val=0 then .panic else .ok ((x.val+1)%256)
 def callThenReturn (x : Byte) : Outcome := match callee x with | .ok _ => .ok 7 | other => other
 def correctInline (x : Byte) : Outcome := if x.val=0 then .panic else .ok 7
 def resultOnlyInline (_x : Byte) : Outcome := .ok 7
 theorem correct (x : Byte) : callThenReturn x = correctInline x := by by_cases h : x.val = 0 <;> simp [callThenReturn, callee, correctInline, h]
 theorem erased_failure : callThenReturn ⟨0,by decide⟩ ≠ resultOnlyInline ⟨0,by decide⟩ := by decide
 theorem error_not_result : (Outcome.ub : Outcome) ≠ .ok 7 := by decide
 theorem divergence_not_error : (Outcome.div : Outcome) ≠ .ub := by decide
 #print axioms correct
 #print axioms erased_failure
 #print axioms error_not_result
 #print axioms divergence_not_error
end Inline
