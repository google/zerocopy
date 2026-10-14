import CapturedFuns
open Aeneas Aeneas.Std Result
def wrongUpdate (p : Std.U8 × Std.U8) (x : Std.U8) : Result (Std.U8 × Std.U8) := ok (x,p.2)
example (p : Std.U8 × Std.U8) (x : Std.U8) : wrongUpdate p x = CertificateProbe.update_second p x := by cases p; rfl
