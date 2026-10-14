import CapturedFuns
open Aeneas Aeneas.Std Result
namespace ActualCounterexamples
def zero : Std.U8 := ⟨⟨0, by decide⟩⟩
def one : Std.U8 := ⟨⟨1, by decide⟩⟩
def two : Std.U8 := ⟨⟨2, by decide⟩⟩
def value (r : Result Std.U8) : Nat := match r with
 | .ok x => x.bv.toNat
 | _ => 999
def first (r : Result (Std.U8 × Std.U8)) : Nat := match r with
 | .ok p => p.1.bv.toNat
 | _ => 999
theorem changed_branch : value (ok one) ≠ value (CertificateProbe.choose true zero one) := by decide
theorem changed_field : first (ok (two, one)) ≠ first (CertificateProbe.update_second (zero, one) two) := by decide
#print axioms changed_branch
#print axioms changed_field
end ActualCounterexamples
