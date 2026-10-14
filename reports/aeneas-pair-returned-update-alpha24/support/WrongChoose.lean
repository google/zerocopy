import CapturedFuns
open Aeneas Aeneas.Std Result
def wrongChoose (b : Bool) (x y : Std.U8) : Result Std.U8 := if b then ok y else ok x
example (b : Bool) (x y : Std.U8) : wrongChoose b x y = CertificateProbe.choose b x y := by cases b <;> rfl
